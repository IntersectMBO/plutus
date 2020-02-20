{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
module Language.PlutusIR.Transform.LetFloat (floatTerm) where

import           Language.PlutusIR
import           Language.PlutusIR.Analysis.Dependencies
import           Language.PlutusIR.Free

import           Control.Lens
import           Control.Monad.RWS
import           Control.Monad.State
import           Data.Foldable                           (traverse_)

import qualified Language.PlutusCore                     as PLC
import qualified Language.PlutusCore.Name                as PLC

import qualified Algebra.Graph.AdjacencyMap              as AM
import qualified Algebra.Graph.AdjacencyMap.Algorithm    as AM
import qualified Algebra.Graph.NonEmpty.AdjacencyMap     as AMN (vertexSet)

import qualified Data.IntMap                             as IM
import qualified Data.Map                                as M
import qualified Data.Set                                as S

-- | For each Let-binding we compute its minimum "rank", which refers to a dependant lambda/Lambda location that this Let-rhs can topmost/highest float upwards to (w/o having out-of-scope errors)
-- In other words, this is a pointer to a lambda location in the PIR program.
type Rank = ( Int               -- ^ the depth of the lambda dep
            , PLC.Unique        -- ^ the name of the lambda dep
            )
          -- TODO: add instance Monoid Rank

-- | During the first pass of the AST, a reader context holds the current in-scope stack of lambdas, as "potential ranks" for consideration.
type Ctx = [Rank] -- the enclosing lambdas in scope that surround a let

-- | During the first pass of the AST, we accumulate into a state the minimum rank of each lets encountered.
type RankData = M.Map
                 PLC.Unique -- ^ the identifier introduced by a let-binding
                 ( Rank-- ^ the minimum rank for this let binding, i.e. where this identifier can topmost/highest float upwards to
                 , PLC.Unique   -- ^ a principal name for this binding, used only because a let-Datatype-bind can introduce multiple identifiers
                 )
-- | During the second pass of the AST, we transform the 'RankData' to an assoc. list of depth=>lambda=>{let_unique} mappings left to process. This assoc. list is sorted by depth for easier code generation.
type DepthData = [(Int,         -- ^ the depth
                    M.Map       -- ^ a mapping of lambdanames belonging to this depth => letidentifiers to float
                      PLC.Unique    -- ^ a lambda name
                      (S.Set PLC.Unique)  -- ^ the let bindings that should be floated/placed under this lambda
                  )
                 ]

-- | A simple table holding a let identifier to its RHS (a triple of annotation, recursivity, binding).
type LetTable tyname name a = M.Map PLC.Unique (a, Recursivity, Binding tyname name a)

-- | An arbitrary-minimal rank to signify that a let-binding has no lambda deps, and thus is allowed to float at the *toplevel* of the PIR program.
topRank :: Rank
topRank = ( 0                               -- ^ depth of the toplevel
          , PLC.Unique { PLC.unUnique = -1} -- ^ a dummy unique
          )

-- | This function takes a 'Term', cleans the 'Term' from all its 'Let'-bindings and stores those lets into a separate table.
-- Note: the output term is most-likely not a valid PIR program anymore.
removeLets :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
            => Term tyname name a
            -> (Term tyname name a, LetTable tyname name a)
removeLets = flip runState M.empty . removeLets'
 where removeLets' = \case
         -- this overrides the 'termSubterms' functionality only for the 'Let' constructor
         Let a r bs tIn -> do
           bs' <- traverse (bindingSubterms removeLets') bs
           let newMap = M.fromList $ fmap (\ b -> (bindingUnique b, (a,r,b))) bs'
           modify (M.union newMap)
           removeLets' tIn
         t -> termSubterms removeLets' t

-- | Traverses a Term to create a mapping of every let variable inside the term ==> to its corresponding rank.
compRanks ::  (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
              => Term tyname name a -> RankData
compRanks pir = fst $ execRWS (compRanks' pir :: RWS Ctx () RankData ()) [] M.empty
 where
  addMaxRank freeVars n = do
    lamRanks <- M.fromList . map (\ l -> (snd l, (l, snd l))) <$> ask
    modify (\ letRanks -> M.insert
                          (n^.PLC.unique.coerced)
                          -- Take the maximum rank of all free vars as the current rank of the let, or TopRank if no free var deps
                          ( let freeRanks = M.restrictKeys (letRanks `M.union` lamRanks) freeVars
                            in if M.null freeRanks -- TODO: fold :: Monoid
                               then topRank
                               else fst $ maximum freeRanks
                          , n^.PLC.unique.coerced)

                          letRanks)

  compRanks' = \case
    Let _ NonRec bs tIn -> do
      traverse_ (\case
                    TermBind _ _ (VarDecl _ n ty) rhs -> do
                      compRanks' rhs -- TODO: perhaps move this to the end of the traversal
                      let freeVars = fType ty `S.union` fTerm rhs -- TODO: We traverse too much the AST here , in quadratic time.
                        in addMaxRank freeVars n

                    TypeBind _ (TyVarDecl _ n _k) tyRhs ->
                      let freeVars = fType tyRhs
                      in addMaxRank freeVars n

                    DatatypeBind _ dt@(Datatype _ _tvdecl _tvdecls n vdecls) -> do
                      lamRanks <- M.fromList . map (\ l -> (snd l, (l, snd l))) <$> ask
                      let freeVars = foldMap (\(VarDecl _ _ ty) -> fType ty) vdecls
                      modify (\ letRanks ->
                                 let allFreeRanks = M.restrictKeys (letRanks `M.union` lamRanks) freeVars
                                     newValue = (if M.null allFreeRanks -- TODO: fold :: Monoid
                                                 then topRank
                                                 else fst $ maximum allFreeRanks
                                                , n^.PLC.unique.coerced) -- the principal data name
                                 in foldr (\ i -> M.insert i newValue) letRanks $ datatypeIds dt)
                ) bs
      compRanks' tIn

    Let _ Rec bs tIn -> do
      lamRanks <- M.fromList . map (\ l -> (snd l, (l, snd l))) <$> ask
      indivFreeVars <- S.unions <$> traverse (\case
                                           TermBind _ _ (VarDecl _ _ ty) rhs -> do
                                             compRanks' rhs -- TODO: perhaps move this to the end of the traversal
                                             pure $ fType ty `S.union` fTerm rhs -- TODO: We traverse too much the AST here , in quadratic time.
                                           TypeBind _ _ tyRhs -> pure $ fType tyRhs
                                           DatatypeBind _ (Datatype _ _ _ _ vdecls) -> pure $ foldMap (\(VarDecl _ _ ty) -> fType ty) vdecls
                                       ) bs
      let groupFreeVars = foldr (S.delete . bindingUnique) indivFreeVars bs --Remove any free var bounds by the whole current letrec-group

      modify (\ letRanks ->
                let allFreeRanks = M.restrictKeys (letRanks `M.union` lamRanks) groupFreeVars
                      -- Take the maximum rank of all free vars of the whole letrec-group (excluding the vars introduced here), or TopRank if no free var deps
                    maxRank = if M.null allFreeRanks -- TODO: fold :: Monoid
                              then topRank
                              else fst $ maximum allFreeRanks
                in foldl (\ acc b -> case b of
                             DatatypeBind _ dt -> foldr (\ i -> M.insert i (maxRank, bindingUnique b)) acc $ datatypeIds dt
                             _ -> M.insert (bindingUnique b) (maxRank, bindingUnique b) acc) letRanks bs --every let bound by this group get the same shared maximum ranking.
             )

      compRanks' tIn

    TyAbs _ n _ t -> withLam n $ compRanks' t
    LamAbs _ n _ t -> withLam n $ compRanks' t

    x -> traverse_ compRanks' (x ^.. termSubterms)

  withLam n = local (\ ctx ->  ( case ctx of
                                   []      -> 1 -- depth of toplevel lambda
                                   (d,_):_ -> d+1 -- increase depth
                               , n^.PLC.unique.coerced) : ctx)


floatTerm :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique, Monoid a)
          => Term tyname name a -> Term tyname name a
floatTerm pir =
  let depthData = toDepthData $ compRanks pir -- run the first pass
  in visitBody (topRank^._1) depthData (topRank^._2) pirClean
 where
  -- Visiting a term to apply the float transformation
  visitTerm curDepth remInfo = \case
      LamAbs a n ty tBody -> LamAbs a n ty $ visitBody  (curDepth+1) remInfo (n ^. PLC.unique . coerced) tBody
      TyAbs a n k tBody  -> TyAbs a n k $ visitBody  (curDepth+1)  remInfo (n ^. PLC.unique . coerced) tBody
      t -> over termSubterms (visitTerm curDepth remInfo) t -- descend

  -- Special case of 'visitTerm' where we visit a lambda or a Lambda body
  visitBody _  [] _ tBody = tBody -- no lets are left to float, do not descend
  visitBody curDepth depthTable@((searchingForDepth, lams_lets):restDepthTable) u tBody
    | curDepth < searchingForDepth = visitTerm curDepth depthTable tBody
    | curDepth == searchingForDepth =
        let tBody' = visitTerm curDepth restDepthTable tBody
        in case M.lookup u lams_lets of
             Just lets -> wrapLets lets curDepth restDepthTable tBody'
             _         -> tBody'
    | otherwise = error "just for completion"

  -- TODO: we can transform easily the above visits to a Reader CurDepth
  -- TODO: using the above pure/local way has the disadvantage that we visit a bit more than we need. To fix this we can use State DepthDataRemaining instead.


  (pirClean, letTable) = removeLets pir

  -- the classic dependency graph, same as the one used by the deadcode elimination transformation
  depGraph = AM.gmap (\case Variable u -> u; _ -> error "just for completion")
             $ AM.removeVertex Root -- we remove Root because we do not care about it right now
             $ runTermDeps pir

  -- the dependency graph, but with datatype-related nodes merged/grouped under a single node per datatypebind a, see 'bindingUnique'.
  reducedDepGraph = M.foldr (\ (_,_,b) accGraph ->
                              case b of
                                DatatypeBind _ dt -> let princ = bindingUnique b
                                                     in foldr (\ assocB -> AM.replaceVertex assocB princ) accGraph $ datatypeIds dt
                                _ -> accGraph) depGraph letTable

  -- take the strongly-connected components of the reduced dep graph, because it may contain loops (introduced by the LetRecs)
  -- topologically sort these sccs, since we rely on linear (sorted) scoping in our 'wrapLets' code generation
  Just topSortedSccs = AM.topSort $ AM.scc reducedDepGraph

  -- | Tries to wrap a given term with newly-generated Let expression(s), essentially floating some Let-Rhses.
  -- The given set of lets is not sorted w.r.t. linear scoping, so this function uses the 'topSortedSccs' of the dependency graph,
  -- to figure out the order in which to generate those new Lets.
  --
  -- The resulting term is wrapped with linear-scope-sorted LetRecs and LetNonRecs (interspersed between each other because letnonrec and letrec syntax cannot be combined)
  -- Example: `let {i = e, ...} in let rec {j = e, ...} in let rec {...} in let {...} in ..... in originalTerm`
  wrapLets lets curDepth restDepthTable t =
    foldl (\ acc dcc ->
             let vs = AMN.vertexSet dcc
             in if vs `S.isSubsetOf` lets -- mandatory check to see if this scc belongs to this rank
                then
                  let newBindings = fmap (\ v -> over bindingSubterms (visitTerm curDepth restDepthTable) ((letTable M.! v)^._3)) $ S.toList vs
                      (mAnn, mRecurs) = foldMap (\ v -> let b = letTable M.! v in (b^._1,b^._2)) vs
                  in case acc of
                       Let accAnn NonRec accBs accIn | mRecurs == NonRec ->
                         -- merge current let-group with previous let-group if both groups' recursivity is nonrec
                         Let (accAnn <> mAnn) NonRec (newBindings ++ accBs) accIn
                       _ ->
                         -- never merge if the previous let-group is a Rec or the current let-group is Rec,
                         -- but nest the current let-group under the previous let-group (above)
                         Let mAnn mRecurs newBindings acc
               else acc -- skip
             ) t topSortedSccs


-- Helpers
----------

toDepthData :: RankData -> DepthData
toDepthData = IM.toAscList . M.foldr (\ ((depth,lamName), letNamePrinc) acc -> IM.insertWith (M.unionWith S.union) depth (M.singleton lamName (S.singleton letNamePrinc)) acc) IM.empty

-- | Returns a single 'Unique' for a particular binding.
-- We need this because datatypebinds introduce multiple identifiers, but we need only one as a key of our 'LetTable',etc. See also: 'datatypeIdentifiers'
--
-- TODO: maybe remove this boilerplate by having a lens "unique" for a Binding
bindingUnique :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique) => Binding tyname name a -> PLC.Unique
bindingUnique = \case TermBind _ _ (VarDecl _ n _) _ -> n ^. PLC.unique . coerced -- just the name coerced
                      TypeBind _ (TyVarDecl _ n _) _ -> n ^. PLC.unique . coerced -- just the name coerced
                      DatatypeBind _ (Datatype _ _ _ n _) -> n ^. PLC.unique . coerced -- arbitrary: uses the match-function's unique as the principal unique of this data binding group

