{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase #-}
module Language.PlutusIR.Transform.FreeFloat where

import Language.PlutusIR

import           Control.Lens
import Data.Foldable (traverse_)

import Control.Monad.RWS


import qualified Language.PlutusCore                as PLC
import qualified Language.PlutusCore.Name        as PLC

import qualified Data.Set as S
import qualified Data.Map as M

type U = PLC.Unique



-- | Each Let has a rank, i.e. the topmost Lambda (location and name) that can enclose the rhs of this Let without having out-of-scope errors
type Rank = ( Int               -- the depth of the lambda dep
            , U                 --  the name of the lambda dep
            )
          -- TODO: add instance Monoid Rank

topRank :: Rank
-- | Lets that do not depend on any lambda can be floated at the toplevel using this rank.
topRank = ( 0
          , PLC.Unique { PLC.unUnique = -1}
          )


type FloatInfo = M.Map
                 U              -- the let name to float
                 Rank       -- the rank that this let can float to

type Ctx = [Rank] -- the enclosing lambdas in scope that surround a let

-- | Traverses a Term to create a mapping of every let variable inside the term ==> to its corresponding rank.
-- It is like the first-pass of the SPJ algorithm.
floatPass1 ::  (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
     => Term tyname name a -> FloatInfo
floatPass1 t = fst $ execRWS (floatPass1' t :: RWS Ctx () FloatInfo ())
               []
               M.empty

floatPass1' :: (MonadReader Ctx m, MonadState FloatInfo m, PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
     => Term tyname name a -> m ()
floatPass1' = \case
    Let _ NonRec bs t -> do
      traverse_ (\case
                    TermBind _ _ (VarDecl _ n _ty) rhs -> do
                      floatPass1' rhs
                      let freeVars = free rhs -- FIXME: We traverse too much the AST here , in quadratic time.
                      lamRanks <- M.fromList . map (\ l -> (snd l, l)) <$> ask
                      modify (\ letRanks -> M.insert
                                            (n^.PLC.unique.coerced)

                                            -- Take the maximum rank of all free vars as the current rank of the let, or TopRank if no free var deps
                                            (let allFreeOccurs = M.restrictKeys (letRanks `M.union` lamRanks) freeVars -- TODO: fold :: Monoid
                                             in if M.null allFreeOccurs
                                                then topRank
                                                else maximum allFreeOccurs)

                                            letRanks)
                    TypeBind _ _ _ -> pure () -- FIXME:
                    DatatypeBind _ _ -> pure () -- FIXME:
                ) bs
      floatPass1' t
    -- FIXME: think about let Rec
    
    -- TODO: abstract repetition
    TyAbs _ n _ t -> local (\ ctx ->  ( case ctx of
                                          [] -> 1
                                          (d,_):_ -> d+1
                                      , n ^. PLC.unique . coerced) : ctx)
                     $ floatPass1' t
    LamAbs _ n _ t -> local (\ ctx ->  ( case ctx of
                                          [] -> 1
                                          (d,_):_ -> d+1
                                      , n ^. PLC.unique . coerced) : ctx)
                     $ floatPass1' t
    x -> traverse_ floatPass1' (x ^.. termSubterms)

-- | Given a term, it returns a set of all the FREE variables inside that term (i.e. not declared/scoped inside the term).
-- FIXME: track also free occurences in TYPES. Now it only works the same as untype lambda calculus
free ::
  (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
  => Term tyname name a -> S.Set U
free = \case
  Var _ x -> S.singleton $ x ^. PLC.unique . coerced

  -- linear scoping on the let non-rec

  -- we don't assume term is renamed, that is why we do this for name shadowing 

  -- TODO: check if termSubterms, termSubtypes can be used and lens + fold

  Let _ NonRec bs tIn -> snd $ foldl (\(accLinearScope,accFreeSet) -> \case
                              TermBind _ _ (VarDecl _ n _ty) tRhs -> ( S.insert (n ^. PLC.unique . coerced) accLinearScope
                                                                     , (free tRhs S.\\ accLinearScope) `S.union` accFreeSet
                                                                     )
                              DatatypeBind _ _ -> (accLinearScope, accFreeSet) -- FIXME: add data type/constructor names  to linear-scope
                              TypeBind _ (TyVarDecl _ n _ty1) _ty -> ( S.insert (n ^. PLC.unique . coerced) accLinearScope
                                                                     , accFreeSet -- FIXME: free(types) as well
                                                                     )
                                     )
                             ( S.empty, free tIn ) bs

  -- all variables in the letrec are scoped
  Let _ Rec bs tIn -> foldl (\acc -> \case
                              TermBind _ _ _ tRhs -> free tRhs `S.union` acc
                              DatatypeBind _ _ -> acc -- - FIXME: add data type/constructor names  to linear-scope
                              TypeBind _ _ _tyRhs -> acc -- FIXME: free(types) as well
                            ) (free tIn) bs
                      S.\\      -- removes all the variable names introduced by this letrec
                      (foldMap (\case
                              TermBind _ _ (VarDecl _ n _ty) _ -> S.singleton (n^.PLC.unique.coerced)
                              DatatypeBind _ _ -> S.empty -- - FIXME: add data type/constructor names  to let-scope
                              TypeBind _ (TyVarDecl _ n _) _Rhs -> S.singleton (n^.PLC.unique.coerced))
                       bs)

  TyAbs _ n _ t -> S.delete (n ^. PLC.unique . coerced) $ free t
  LamAbs _ n _ t -> S.delete (n ^. PLC.unique . coerced) $ free t

  Apply _ t1 t2 -> free t1 `S.union` free t2
  TyInst _ t _ -> free t
  IWrap _ _ _ t -> free t
  Unwrap _ t -> free t
  _ -> S.empty
