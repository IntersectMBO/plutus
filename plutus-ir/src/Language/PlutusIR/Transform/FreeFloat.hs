{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs            #-}
module Language.PlutusIR.Transform.FreeFloat where

import Language.PlutusIR
import Language.PlutusIR.Analysis.Dependencies

import           Control.Lens
import Data.Foldable (traverse_)

import qualified Algebra.Graph.AdjacencyMap           as AM
import qualified Algebra.Graph.AdjacencyMap.Algorithm           as AM
import qualified Algebra.Graph.NonEmpty.AdjacencyMap as AMN

import Control.Monad.RWS
import Control.Monad.State

import qualified Language.PlutusCore                as PLC
import qualified Language.PlutusCore.Name        as PLC

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.IntMap as IM

import Data.List ((\\))
import qualified Data.List.NonEmpty as LN

import Data.Maybe (fromJust)

import Language.PlutusIR.Parser
import Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Transform.Rename          ()
import           Language.PlutusCore.Quote
import Language.PlutusCore.Pretty
import qualified Language.PlutusIR.Analysis.Dependencies as D



-- | Each Let has a rank, i.e. the topmost Lambda (location and name) that can enclose the rhs of this Let without having out-of-scope errors
type Rank = ( Int               -- the depth of the lambda dep
            , PLC.Unique        --  the name of the lambda dep
            )
          -- TODO: add instance Monoid Rank

topRank :: Rank
-- | Lets that do not depend on any lambda can be floated at the toplevel using this rank.
topRank = ( 0
          , PLC.Unique { PLC.unUnique = -1}
          )


type FloatInfo = M.Map
                 PLC.Unique -- an identifier introduced by a let-binding
                 (Rank,--  where this identifier can maximally float upwards to
                  PLC.Unique)   -- the principal name of the binding (because a binding in Data can introduce multiple identifiers)

type DepthInfo = IM.IntMap      -- depth
                 (M.Map PLC.Unique            -- lambda name
                        [PLC.Unique])         -- a series of let bindings (not just identifiers) of this level, unsorted w.r.t. dependency graph

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
    Let _ NonRec bs tIn -> do
      lamRanks <- M.fromList . map (\ l -> (snd l, (l, snd l))) <$> ask
      traverse_ (\case
                    TermBind _ _ (VarDecl _ n ty) rhs -> do
                      floatPass1' rhs -- TODO: perhaps move this to the end of the traversal
                      let freeVars = freeT ty `S.union` free rhs -- TODO: We traverse too much the AST here , in quadratic time.
                      modify (\ letRanks -> M.insert
                                            (n^.PLC.unique.coerced)

                                            -- Take the maximum rank of all free vars as the current rank of the let, or TopRank if no free var deps
                                            ((let allFreeRanks = M.restrictKeys (letRanks `M.union` lamRanks) freeVars -- TODO: fold :: Monoid
                                             in if M.null allFreeRanks
                                                then topRank
                                                else fst $ maximum allFreeRanks), n^.PLC.unique.coerced)

                                            letRanks)
                    TypeBind _ (TyVarDecl _ n _k) tyRhs -> do
                      let freeVars = freeT tyRhs
                      -- TODO: duplicate code
                      modify (\ letRanks -> M.insert
                                            (n^.PLC.unique.coerced)

                                            -- Take the maximum rank of all free vars as the current rank of the let, or TopRank if no free var deps
                                            ((let allFreeRanks = M.restrictKeys (letRanks `M.union` lamRanks) freeVars -- TODO: fold :: Monoid
                                             in if M.null allFreeRanks
                                                then topRank
                                                else fst $ maximum allFreeRanks), n^.PLC.unique.coerced)

                                            letRanks)
                    DatatypeBind _ dt@(Datatype _ _tvdecl _tvdecls n vdecls) -> do
                      let freeVars = foldMap (\(VarDecl _ _ ty) -> freeT ty) vdecls
                      modify (\ letRanks ->
                                 let allFreeRanks = M.restrictKeys (letRanks `M.union` lamRanks) freeVars -- TODO: fold :: Monoid
                                     newValue = (if M.null allFreeRanks
                                                 then topRank
                                                 else fst $ maximum allFreeRanks
                                                , n^.PLC.unique.coerced) -- the principal data name
                                 in foldr (\ i -> M.insert i newValue) letRanks $ datatypeIdentifiers dt)
                ) bs
      floatPass1' tIn

    Let _ Rec bs tIn -> do
      lamRanks <- M.fromList . map (\ l -> (snd l, (l, snd l))) <$> ask
      indivFreeVars <- S.unions <$> traverse (\case
                                           TermBind _ _ (VarDecl _ _ ty) rhs -> do
                                             floatPass1' rhs -- TODO: perhaps move this to the end of the traversal
                                             pure $ freeT ty `S.union` free rhs -- TODO: We traverse too much the AST here , in quadratic time.
                                           TypeBind _ _ tyRhs -> pure $ freeT tyRhs
                                           DatatypeBind _ (Datatype _ _ _ _ vdecls) -> pure $ foldMap (\(VarDecl _ _ ty) -> freeT ty) vdecls
                                       ) bs
      let groupFreeVars = foldr (S.delete . bindingUnique) indivFreeVars bs --Remove any free var bounds by the whole current letrec-group

      modify (\ letRanks ->
                let allFreeRanks = M.restrictKeys (letRanks `M.union` lamRanks) groupFreeVars
                      -- Take the maximum rank of all free vars of the whole letrec-group (excluding the vars introduced here), or TopRank if no free var deps
                    maxRank = if M.null allFreeRanks
                              then topRank
                              else fst $ maximum allFreeRanks
                in foldl (\ acc b -> case b of
                             DatatypeBind _ dt -> foldr (\ i -> M.insert i (maxRank, bindingUnique b)) acc $ datatypeIdentifiers dt
                             _ -> M.insert (bindingUnique b) (maxRank, bindingUnique b) acc) letRanks bs --every let bound by this group get the same shared maximum ranking.
             )

      floatPass1' tIn

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

float :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
           => Term tyname name a -> Term tyname name a
float topTerm = processLam (fst topRank) depthInfo (snd topRank) topTermClean
 where
  floatInfo = floatPass1 topTerm
  depthInfo = IM.toAscList $  toDepthInfo floatInfo
  (topTermClean, letTable) = extractLets topTerm
  depGraph = AM.gmap (\case Variable u -> u; _ -> error "just for completion")
             $ AM.removeVertex Root --we remove Root because we do not care about it right now
             $ runTermDeps topTerm
  sortedSccs = fromJust $ AM.topSort $ AM.scc depGraph :: [AMN.AdjacencyMap PLC.Unique]

  generateLetLvl' lets curDepth restDepthTable tRest =
    foldl (\ acc dcc ->
             case AMN.vertexList1 dcc of
               (v LN.:| []) -> if v `elem` lets
                               then
                                 case acc of
                                   Let _ NonRec accBs accIn -> -- merge with let-nonrec of acc
                                     Let
                                     (fstT $ snd $ M.findMin letTable ) -- FIXME: fix annotation with monoid?
                                     NonRec
                                     (over bindingSubterms (processTerm curDepth restDepthTable) (trdT (letTable M.! v)) : accBs)
                                     accIn
                                   _ ->
                                     Let
                                     (fstT $ snd $ M.findMin letTable ) -- FIXME: fix annotation with monoid?
                                     NonRec
                                     [over bindingSubterms (processTerm curDepth restDepthTable) (trdT (letTable M.! v))]
                                     acc
                               else acc
               vs -> if null (LN.toList vs \\ lets)
                     then
                       Let
                       (fstT $ snd $ M.findMin letTable ) -- FIXME: fix annotation with monoid?
                       Rec
                       (LN.toList $ fmap (\ v -> over bindingSubterms (processTerm curDepth restDepthTable) (trdT (letTable M.! v))) vs)
                       acc
                     else acc -- skip
             ) tRest sortedSccs

  fstT (a,_,_) = a
  trdT (_,_,c) = c

  -- TODO: we can transform easily the following processing to a Reader CurDepth
  -- TODO: using this pure/local way has the disadvantage that we visit a bit more than we need. To fix this we can use State DepthInfoRemaining instead.
  processLam _  [] _ lamBody = lamBody
  processLam curDepth depthTable@((searchingForDepth, lams_lets):restDepthTable) u lamBody =
    if curDepth < searchingForDepth
    then processTerm curDepth depthTable lamBody
    else -- assume/assert curDepth == searchingForDepth
      (case M.lookup u lams_lets of
        Just lets -> generateLetLvl' lets curDepth restDepthTable
        _ -> id)  (processTerm curDepth restDepthTable lamBody)
  processTerm _ [] = id
  processTerm curDepth remInfo =
    \case
      LamAbs a n ty lamBody -> LamAbs a n ty $ processLam  (curDepth+1) remInfo (n ^. PLC.unique . coerced) lamBody
      TyAbs a n k lamBody  -> TyAbs a n k $ processLam  (curDepth+1)  remInfo (n ^. PLC.unique . coerced) lamBody
      Apply a t1 t2 -> Apply a (processTerm curDepth remInfo t1) (processTerm curDepth remInfo t2)
      TyInst a t ty -> TyInst a (processTerm curDepth remInfo t) ty
      IWrap a ty1 ty2 t -> IWrap a ty1 ty2 $ processTerm curDepth remInfo t
      Unwrap a t -> Unwrap a $ processTerm curDepth remInfo t
      x -> x


-- | Given a term, it returns a set of all the FREE variables inside that term (i.e. not declared/scoped inside the term).
free ::
  (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
  => Term tyname name a -> S.Set PLC.Unique
free = \case
  Var _ x -> S.singleton $ x ^. PLC.unique . coerced

  -- linear scoping on the let non-rec

  -- we don't assume term is renamed, that is why we do this for name shadowing 

  -- TODO: check if termSubterms, termSubtypes can be used and lens + fold

  Let _ NonRec bs tIn -> snd $ foldl (\(accLinearScope,accFreeSet) -> \case
                              TermBind _ _ (VarDecl _ n ty) tRhs -> ( S.insert (n ^. PLC.unique . coerced) accLinearScope
                                                                     , (S.union (freeT ty) (free tRhs) S.\\ accLinearScope) `S.union` accFreeSet
                                                                     )
                              DatatypeBind _ dt@(Datatype _ _ _ _ vdecls) -> (
                                -- new linear scope is the introduced identifiers plus the old linear scope
                                -- add to the next linear scope, all the newly introduced identifiers
                                S.fromList (datatypeIdentifiers dt) `S.union` accLinearScope,

                                -- all Ty occurences of this databind - the previous linear scope
                                (S.unions (fmap (\(VarDecl _ _ ty) -> freeT ty) vdecls) S.\\ accLinearScope) `S.union` accFreeSet
                                )
                              TypeBind _ (TyVarDecl _ n _k) tyRhs -> ( S.insert (n ^. PLC.unique . coerced) accLinearScope
                                                                     , (freeT tyRhs S.\\ accLinearScope) `S.union` accFreeSet
                                                                     )
                                     )
                             ( S.empty,
                               free tIn
                               S.\\   -- removes all the identifiers introduced by this letnonrec
                               (foldMap (\case
                                            TermBind _ _ (VarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced)
                                            DatatypeBind _ dt -> S.fromList $ datatypeIdentifiers dt
                                            TypeBind _ (TyVarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced))
                                bs)
                             ) bs

  -- all variables in the letrec are scoped
  Let _ Rec bs tIn -> foldl (\acc -> \case
                              TermBind _ _ (VarDecl _ _ ty) tRhs -> S.unions [freeT ty, free tRhs, acc]
                              DatatypeBind _ (Datatype _ _ _ _ vdecls) -> S.unions $ fmap (\(VarDecl _ _ ty) -> freeT ty) vdecls
                              TypeBind _ (TyVarDecl _ _ _k) tyRhs -> freeT tyRhs `S.union` acc
                            ) (free tIn) bs
                      S.\\      -- removes all the variable names introduced by this letrec
                      -- TODO: duplicate code
                      (foldMap (\case
                              TermBind _ _ (VarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced)
                              DatatypeBind _ dt -> S.fromList $ datatypeIdentifiers dt
                              TypeBind _ (TyVarDecl _ n _) _ -> S.singleton (n^.PLC.unique.coerced))
                       bs)

  TyAbs _ n _ t -> S.delete (n ^. PLC.unique . coerced) $ free t
  LamAbs _ n ty t -> freeT ty
                     `S.union`
                     S.delete (n ^. PLC.unique . coerced) (free t)
  Apply _ t1 t2 -> free t1 `S.union` free t2
  TyInst _ t ty -> free t `S.union` freeT ty
  IWrap _ ty1 ty2 t -> S.unions [freeT ty1, freeT ty2, free t]
  Unwrap _ t -> free t
  _ -> S.empty


freeT :: (PLC.HasUnique (tyname a) PLC.TypeUnique)
  => Type tyname a -> S.Set PLC.Unique
freeT = \case
  -- occurences
  TyVar _ n -> S.singleton $ n ^. PLC.unique . coerced
  TyForall _ n _k ty -> S.insert (n ^. PLC.unique . coerced) $ freeT ty

  -- introduction of type, thus ignore sub-occurrences
  TyLam _ n _k ty -> S.delete (n ^. PLC.unique . coerced) $ freeT ty

  TyFun _ ty1 ty2 -> S.union (freeT ty1) (freeT ty2)
  TyIFix _ ty1 ty2 -> S.union (freeT ty1) (freeT ty2)
  TyApp _ ty1 ty2 -> S.union (freeT ty1) (freeT ty2)
  TyBuiltin _ _ -> S.empty

toDepthInfo :: FloatInfo -> DepthInfo
toDepthInfo = M.foldr (\ ((depth,lamName),letName) acc -> IM.insertWith (M.unionWith (++)) depth (M.singleton lamName [letName]) acc) IM.empty




-- | A table from a let-introduced identifier to its RHS.
type LetTable tyname name a = M.Map PLC.Unique (a, Recursivity, Binding tyname name a)

-- | This function takes a 'Term' and returns the same 'Term' but with all 'Let'-bindings removed and stored into a separate table.
extractLets :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
                    => Term tyname name a
                    -> (Term tyname name a
                       ,LetTable tyname name a
                       )
extractLets = flip runState M.empty . extractLets'
 where
    extractLets' :: (Monad m, PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
                  => Term tyname name a
                  -> StateT (LetTable tyname name a) m (Term tyname name a)
    extractLets' = \case
          -- this overrides the 'termSubterms' functionality only for the 'Let' constructor
          Let a r bs t' -> do

            bs' <- traverse (bindingSubterms extractLets') bs

            let newMap = M.fromList $
                                fmap (\ b -> (bindingUnique b, (a,r,b))) bs'

            modify (M.union newMap)

            extractLets' t'

          t -> termSubterms extractLets' t

-- | return a single 'Unique' for a particular binding.
-- TODO: maybe remove this boilerplate by having a lens "name" for a Binding
bindingUnique :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique) => Binding tyname name a -> PLC.Unique
bindingUnique = \case TermBind _ _ (VarDecl _ n _) _ -> n ^. PLC.unique . coerced
                      TypeBind _ (TyVarDecl _ n _) _ -> n ^. PLC.unique . coerced
                      DatatypeBind _ (Datatype _ _ _ n _) -> n ^. PLC.unique . coerced -- arbitrary: use the match-function-name as the principal name of the data binding group

datatypeIdentifiers :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique) => Datatype tyname name a ->  [PLC.Unique] -- TODO: Change it to Set
datatypeIdentifiers (Datatype _ tvdecl tvdecls n vdecls) =
  n^.PLC.unique.coerced
  : fmap (\(TyVarDecl _ tn _) ->tn^.PLC.unique.coerced) (tvdecl:tvdecls)
  ++ fmap (\(VarDecl _ vn _)->vn^.PLC.unique.coerced) vdecls
