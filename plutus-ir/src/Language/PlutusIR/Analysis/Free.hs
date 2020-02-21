{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module Language.PlutusIR.Analysis.Free (fTerm, fType) where

import           Language.PlutusIR

import qualified Language.PlutusCore       as PLC
import qualified Language.PlutusCore.Name  as PLC

import           Language.PlutusCore.Subst (ftvTy)

import           Control.Lens

import qualified Data.Set                  as S

-- | Given a term, it returns a set of all the FREE variables inside that term (i.e. not declared/scoped inside the term).
-- TODO: refactor using recursion-schemes (or usingtermSubterms, termSubtypes can be used and lens + fold), see 'language-plutus-core/src/Language/PlutusCore/Subst.hs'
fTerm ::
  (Ord (tyname a), PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
  => Term tyname name a -> S.Set PLC.Unique
fTerm = \case
  Var _ x -> S.singleton $ x ^. PLC.unique . coerced

  -- linear scoping on the let non-rec
  -- we don't assume term is renamed, that is why we do this scoping-accumulation for name shadowing
  Let _ NonRec bs tIn -> snd $ foldl (\(accLinearScope,accFreeSet) -> \case
                              TermBind _ _ (VarDecl _ n ty) tRhs -> ( S.insert (n ^. PLC.unique . coerced) accLinearScope
                                                                     , (S.union (fType ty) (fTerm tRhs) S.\\ accLinearScope) `S.union` accFreeSet
                                                                     )
                              DatatypeBind _ dt@(Datatype _ _ _ _ vdecls) -> (
                                -- new linear scope is the introduced identifiers plus the old linear scope
                                -- add to the next linear scope, all the newly introduced identifiers
                                datatypeIds dt `S.union` accLinearScope,

                                -- all Ty occurences of this databind - the previous linear scope
                                (S.unions (fmap (\(VarDecl _ _ ty) -> fType ty) vdecls) S.\\ accLinearScope) `S.union` accFreeSet
                                )
                              TypeBind _ (TyVarDecl _ n _k) tyRhs -> ( S.insert (n ^. PLC.unique . coerced) accLinearScope
                                                                     , (fType tyRhs S.\\ accLinearScope) `S.union` accFreeSet
                                                                     )
                                     )
                             ( S.empty,
                               fTerm tIn
                               S.\\   -- removes all the identifiers introduced by this letnonrec
                               (foldMap (\case
                                            TermBind _ _ (VarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced)
                                            DatatypeBind _ dt -> datatypeIds dt
                                            TypeBind _ (TyVarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced))
                                bs)
                             ) bs

  -- all variables in the letrec are scoped
  Let _ Rec bs tIn -> foldl (\acc -> \case
                              TermBind _ _ (VarDecl _ _ ty) tRhs -> S.unions [fType ty, fTerm tRhs, acc]
                              DatatypeBind _ (Datatype _ _ _ _ vdecls) -> S.unions $ fmap (\(VarDecl _ _ ty) -> fType ty) vdecls
                              TypeBind _ (TyVarDecl _ _ _k) tyRhs -> fType tyRhs `S.union` acc
                            ) (fTerm tIn) bs
                      S.\\      -- removes all the variable names introduced by this letrec
                      -- TODO: duplicate code
                      (foldMap (\case
                              TermBind _ _ (VarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced)
                              DatatypeBind _ dt -> datatypeIds dt
                              TypeBind _ (TyVarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced))
                       bs)

  TyAbs _ n _ t -> S.delete (n ^. PLC.unique . coerced) $ fTerm t
  LamAbs _ n ty t -> fType ty
                     `S.union`
                     S.delete (n ^. PLC.unique . coerced) (fTerm t)
  Apply _ t1 t2 -> fTerm t1 `S.union` fTerm t2
  TyInst _ t ty -> fTerm t `S.union` fType ty
  IWrap _ ty1 ty2 t -> S.unions [fType ty1, fType ty2, fTerm t]
  Unwrap _ t -> fTerm t
  _ -> S.empty


fType :: (Ord (tyname a), PLC.HasUnique (tyname a) PLC.TypeUnique)
  => Type tyname a -> S.Set PLC.Unique
fType = S.map (^. PLC.unique . coerced) . ftvTy
