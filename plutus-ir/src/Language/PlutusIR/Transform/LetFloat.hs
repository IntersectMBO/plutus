{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
module Language.PlutusIR.Transform.LetFloat (floatTerm) where

import           Language.PlutusIR
import           Language.PlutusIR.Analysis.Dependencies
import           Language.PlutusIR.Analysis.Free

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.RWS
import           Control.Monad.State

import qualified Language.PlutusCore                     as PLC
import qualified Language.PlutusCore.Name                as PLC

import qualified Algebra.Graph.AdjacencyMap              as AM
import qualified Algebra.Graph.AdjacencyMap.Algorithm    as AM
import qualified Algebra.Graph.NonEmpty.AdjacencyMap     as AMN

import           Data.Foldable                           (fold)
import qualified Data.IntMap                             as IM
import qualified Data.Map                                as M
import           Data.Maybe                              (fromMaybe)
import qualified Data.Set                                as S
import Data.Function (on)

-- | For each Let-binding we compute its minimum "rank", which refers to a dependant lambda/Lambda location that this Let-rhs can topmost/highest float upwards to (w/o having out-of-scope errors)
-- In other words, this is a pointer to a lambda location in the PIR program.
data Rank = Top
          | LamDep Int PLC.Unique
          deriving Eq

-- | usual getter function
_depth :: Rank -> Int
_depth = \case
  Top -> 0
  LamDep d _ -> d

-- | lens-style getter
depth :: Getting r Rank Int
depth  = to _depth

instance Ord Rank where
  compare = compare `on` _depth

-- acts like a Data.Semigroup.Max
instance Semigroup Rank where
  r1 <> r2 = max r1 r2

instance Monoid Rank where
  mempty = Top

-- | During the first pass of the AST, a reader context holds the current in-scope stack of lambdas, as "potential ranks" for consideration.
type Ctx = (RankData, Int) -- the enclosing lambdas in scope that surround a let

-- | During the first pass of the AST, we accumulate into a state the minimum rank of each lets encountered.
type RankData = M.Map
                 PLC.Unique -- ^ the identifier introduced by a let-binding
                 ( Rank-- ^ the minimum rank for this let binding, i.e. where this identifier can topmost/highest float upwards to
                 , PLC.Unique   -- ^ a principal name for this binding, used only because a let-Datatype-bind can introduce multiple identifiers
                 )

-- | During the second pass of the AST, we transform the 'RankData' to an assoc. list of depth=>lambda=>{let_unique} mappings left to process. This assoc. list is sorted by depth for easier code generation.
type DepthData = IM.IntMap -- ^ the depth (starting from 0, which is Top)
                    (M.Map       -- ^ a mapping of locations belonging to this depth => letidentifiers to float
                      Rank    -- ^ the location where the let should float to: location is a lambda name or Top
                      (S.Set PLC.Unique) -- ^ the let bindings that should be floated/placed under this lambda or Top
                    )

-- | A simple table holding a let-introduced identifier to its RHS.
--
-- Let-groups do not exist in this representation.
-- The Recursivity&Annotation of a prior let-group are copied to each of its RHS entry in the table.
type RhsTable tyname name a = M.Map
                              PLC.Unique
                              (Rhs tyname name a)

-- | An Rhs is a triple of Annotation, Recursivity, and its Binding.
--
-- If the RHS was prior belonging to a let-group, its Recursivity&Annotation refers to (is copied from) the let-group's Recursivity&Annotation.
type Rhs tyname name ann = (ann, Recursivity, Binding tyname name ann)

-- | This function takes a 'Term', cleans the 'Term' from all its 'Let'-bindings and stores those lets into a separate table.
-- Note: the output term is most-likely not a valid PIR program anymore.
removeLets :: forall name tyname a
            . (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
           => Term tyname name a
           -> (Term tyname name a, RhsTable tyname name a)
removeLets = flip runState M.empty . go
 where
   go :: Term tyname name a -> State (RhsTable tyname name a) (Term tyname name a)
   go = \case
         -- this overrides the 'termSubterms' functionality only for the 'Let' constructor
         Let a r bs tIn -> do
           forM_ bs $ \ b -> do
             b' <- bindingSubterms go b
             modify (M.insert (b'^.princUnique) (a, r, b'))
           go tIn
         t -> termSubterms go t

-- | First-pass: Traverses a Term to create a mapping of every let variable inside the term ==> to its corresponding rank.
p1Term ::  forall name tyname a
           . (Ord (tyname a), PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
          => Term tyname name a -> RankData
p1Term pir = runReader (goTerm pir) (M.empty, 0)

  where

    goTerm :: Term tyname name a
        -> Reader Ctx RankData
    goTerm = \case
      LamAbs _ n _ tBody  -> goBody n tBody
      TyAbs _ n _ tBody   -> goBody n tBody

      Let _ Rec bs tIn    -> goRec bs tIn
      Let _ NonRec bs tIn -> goNonRec bs tIn

      -- recurse and then accumulate the return values
      Apply _ t1 t2 -> (<>) <$> goTerm t1 <*> goTerm t2
      TyInst _ t _ -> goTerm t
      IWrap _ _ _ t -> goTerm t
      Unwrap _ t -> goTerm t

      -- "ground" terms (terms that do not contain other terms)
      _ -> asks fst -- the ctx's rankdata is propagated back upwards as the return value

    goBody :: PLC.HasUnique b b' => b -> Term tyname name a -> Reader Ctx RankData
    goBody n tBody =
      let lamName= n^.PLC.unique.coerced
      in M.delete lamName -- this rick removes any lamrank from the final value, since we don't care about lambdas in the final pass1 result (RankData)
         <$> (local (\ (scope,oldDepth) ->
                        let newDepth = oldDepth+1
                            newRank = LamDep newDepth lamName
                            newScope = M.insert lamName (newRank,lamName) scope -- adds a new lam rank to the current scope
                        in (newScope, newDepth))
                    $ goTerm tBody)

    goRec :: [Binding tyname name a] -> Term tyname name a -> Reader Ctx RankData
    goRec bs tIn = do
        -- the freevars is the union of each binding's freeVars,
        -- excluding the newly-introduced binding identifiers of this letrec
        let freeVars = foldMap fBinding bs S.\\ foldMap bindingIds bs
        -- all bindings share their commonly-maximum rank
        newScope <- addRanks bs freeVars
        resBs <- mconcat <$> forM (bs^..traverse.bindingSubterms)
                                  (withScope newScope . goTerm)
        resIn <- withScope newScope $ goTerm tIn
        pure $ resBs <> resIn

    goNonRec :: [Binding tyname name a] -> Term tyname name a -> Reader Ctx RankData
    goNonRec bs tIn = do
      foldr (\ b acc -> do
           -- this means that we see each binding individually, not at the whole let level
           let freeVars = fBinding b
           -- compute a maxrank for this binding alone and a newscope that includes it
           newScope <- addRanks [b] freeVars
           resHead <- mconcat <$> forM (b^..bindingSubterms) goTerm
           resRest <- withScope newScope $ acc
           pure $ resHead <> resRest
       ) (goTerm tIn) bs


    -- | Given a set of bindings and the union of their free-variables,
    -- compute their maximum,common free-variable (Rank),
    -- and rank these bindings by adding them to the current scope (RankData)
    addRanks :: [Binding tyname name a] -- ^ bindings
             -> S.Set PLC.Unique -- ^ their free-vars
             -> Reader Ctx RankData -- ^ the updated scope that includes the added ranks
    addRanks bs freeVars = do
      (scope, _) <- ask
      let
          -- the ranks of the free variables
          freeRanks = fmap fst $ M.restrictKeys scope freeVars
          -- the max rank from all their free variables
          maxRank = fold freeRanks
          -- this computed max rank is linked/associated to all the given bindings and added to the current scope
          newScope = foldr (\ b -> M.insert (b^.princUnique) (maxRank, b^.princUnique)) scope bs
      pure newScope


    withScope :: RankData -> Reader Ctx b -> Reader Ctx b
    withScope s = local (set _1 s) -- changes only the scope (i.e. rankdata in our case)


-- OPTIMIZE: We could potentially replace the pure descending of DepthData (Reader DepthData) to a State DepthData. In such a case
-- this transformation might stop earlier, when the state becomes empty: i.e. no let-rhses left to float.
floatTerm :: forall name tyname a.
             (Ord (tyname a), PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique, Monoid a)
             => Term tyname name a -> Term tyname name a
floatTerm pir =
    let topLoc = mempty  -- starting from the top-level
    in goBody topLoc depthData pirClean -- start by trying to float some lets at the top-level
 where

  -- | Visiting each term to apply the float transformation
  goTerm :: Int -- ^ current depth
         -> [(Int, M.Map Rank (S.Set PLC.Unique))] -- ^ the lambdas we are searching for (to float some lets inside them)
         -> Term tyname name a
         -> Term tyname name a
  goTerm curDepth searchTable = \case
      -- we are only interested in lambdas/Lambdas
      LamAbs a n ty tBody -> LamAbs a n ty $ goAbs curDepth searchTable n tBody
      TyAbs a n k tBody  -> TyAbs a n k $ goAbs curDepth searchTable n tBody
      -- descend otherwise to apply the transformations to subterms
      t -> over termSubterms (goTerm curDepth searchTable) t

  -- | The function just updates the current location (depth+lamname) and visits its body
  goAbs :: PLC.HasUnique b b'
        => Int -- ^ current depth
        -> [(Int, M.Map Rank (S.Set PLC.Unique))] -- ^ the lambdas we are searching for (to float some lets inside them)
        -> b                                            -- ^ lambda/Lambda's name
        -> Term tyname name a                           -- ^ lambda/Lambda's body
        -> Term tyname name a
  goAbs oldDepth searchTable n tBody =
    let newLam = LamDep (oldDepth+1) (n^.PLC.unique.coerced)
    in goBody newLam searchTable tBody

  -- | We are currently INSIDE (exactly under) a lambda/Lambda body/Top (Top if we are right at the start of the algorithm)
  -- We try to see if we have some lets to float here based on our 1st-pass-table data (searchTable).
  goBody :: Rank -- ^ the rank/location of the lambda above that has this body
         -> [(Int, M.Map Rank (S.Set PLC.Unique))] -- ^ the lambdas we are searching for (to float some lets inside them)
         -> Term tyname name a                           -- ^ the body term
         -> Term tyname name a                           -- ^ the transformed body term
  goBody _  [] tBody = tBody -- no lets are left to float, do not descend
  goBody aboveLamLoc searchTable@( (searchingForDepth, searchingForLams_Lets) : restSearchTable) tBody =
    let curDepth = aboveLamLoc^.depth
    in case curDepth `compare` searchingForDepth of
      -- the minimum next depth we are looking for, is not this one, so just descend
      LT -> goTerm curDepth searchTable tBody
      -- found depth, see if our lambda above is a lambda we are interested in (to float some lets)
      EQ ->
        -- transform the lambody, passing the rest table
        let tBody' = goTerm curDepth restSearchTable tBody
        in case M.lookup aboveLamLoc searchingForLams_Lets of
             -- the lambda above-this-body has some let-rhses to insert (float) here.
             Just lets -> wrapLets lets curDepth restSearchTable tBody'
             -- nothing to do for the lambda above, i.e. no let-rhses to insert here
             _         -> tBody'
      GT -> error "This shouldn't happen, because the algorithm takes care to stop descending when EQ is reached."



  depthData :: [(IM.Key, M.Map Rank (S.Set PLC.Unique))]
  depthData = IM.toAscList $ toDepthData $ p1Term pir -- run the first pass


  (pirClean :: Term tyname name a, rhsTable :: RhsTable tyname name a) = removeLets pir

  -- | the dependency graph (as the one used by the deadcode elimination)
  -- but w/o the root node and only uses the name of the var (PLC.Unique) as the node id
  depGraph :: AM.AdjacencyMap PLC.Unique
  depGraph = AM.gmap (\case Variable u -> u; _ -> error "just for completion")
             $ AM.removeVertex Root -- we remove Root because we do not care about it
             $ runTermDeps pir

  -- | the dependency graph as before, but with datatype-related nodes merged/grouped under a single node per datatypebind a, see 'bindingUnique'.
  reducedDepGraph :: AM.AdjacencyMap PLC.Unique
  reducedDepGraph = M.foldr (\ (_,_,b) accGraph ->
                              case b of
                                DatatypeBind _ dt -> let princ = b^.princUnique
                                                     in foldr (\ assocB -> AM.replaceVertex assocB princ) accGraph $ datatypeIds dt
                                _ -> accGraph) depGraph rhsTable

  -- |take the strongly-connected components of the reduced dep graph, because it may contain loops (introduced by the LetRecs)
  -- topologically sort these sccs, since we rely on linear (sorted) scoping in our 'wrapLets' code generation
  topSortedSccs :: [AMN.AdjacencyMap PLC.Unique]
  topSortedSccs = fromMaybe (error "Cycle detected in the depgraph. This shouldn't happen in the first place.") $ AM.topSort $ AM.scc reducedDepGraph

  -- | Groups a given set of lets into one or more multilets and wraps these multilets around a given term.
  -- The grouping is done through the strongly-connected components
  -- The input lets is not sorted w.r.t. linear scoping, so this function uses the topological-sort of these SCCs
  -- to figure out the correct (dependend/linear) order in which to generate these new multilets.
  --
  -- Note that the resulting term is wrapped with linear-scope-sorted LetRecs and LetNonRecs (interspersed between each other because letnonrec and letrec syntax cannot be combined)
  -- Example: `let {i = e, ...} in let rec {j = e, ...} in let rec {...} in let {...} in ..... in originalTerm`
  wrapLets :: S.Set PLC.Unique -- ^ all the let identifiers to wrap around this term
           -> Int -- ^ current depth
           -> [(Int, M.Map Rank (S.Set PLC.Unique))] -- ^ the table remaining
           -> Term tyname name a                           -- ^ the term to be wrapped
           -> Term tyname name a                           -- ^ the final wrapped term
  wrapLets lets curDepth restDepthTable t =
    foldl (\ acc scc ->
             let vs = AMN.vertexSet scc
             in if vs `S.isSubsetOf` lets -- mandatory check to see if this scc belongs to this rank, because we fold over all sccs
                then -- Recursively float all terms of RHSes.
                     -- Group the transformed RHSes into a new let-group (since they depend on each other).
                     -- The group gets a common annotation, recursion and a GROUPING (i.e. list) of transformed bindings of the RHSes
                     let (mAnn, mRecurs, newBindings) =
                           foldMap (\ v ->
                                       case M.lookup v rhsTable of
                                         Just rhs ->
                                           -- lift each resulting binding in a list monoid to accumulate them
                                           over _3 pure $
                                           -- visit the generated rhs-term as well for any potential floating
                                           over (_3.bindingSubterms)
                                                (goTerm curDepth restDepthTable)
                                                rhs
                                         _ -> error "Something went wrong: no rhs was found for this let in the rhstable."
                                   ) vs
                     in case acc of
                       -- merge current let-group with previous let-group iff both groups' recursivity is NonRec
                       Let accAnn NonRec accBs accIn | mRecurs == NonRec -> Let (mAnn <> accAnn) NonRec (newBindings <> accBs) accIn
                       -- never merge if the previous let-group is a Rec or the current let-group is Rec,
                       -- but instead create a nested current let-group under the previous let-group (above)
                       _ -> Let mAnn mRecurs newBindings acc
               else acc -- skip this scc, we are not interested in it right now
             ) t topSortedSccs


-- Helpers
----------

toDepthData :: RankData -> DepthData
toDepthData = foldr (\ (dep, letNamePrinc) acc -> IM.insertWith (M.unionWith (<>)) (dep^.depth) (M.singleton dep (S.singleton letNamePrinc)) acc) IM.empty

-- | Returns a single 'Unique' for a particular binding.
-- We need this because datatypebinds introduce multiple identifiers, but we need only one as a key of our 'RhsTable',etc. See also: 'datatypeIdentifiers'
--
-- TODO: Getter for a lens "unique" for a Binding
princUnique :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
            => Getting r (Binding tyname name a) PLC.Unique
princUnique = to $ \case TermBind _ _ (VarDecl _ n _) _ -> n ^. PLC.unique . coerced -- just the name coerced
                         TypeBind _ (TyVarDecl _ n _) _ -> n ^. PLC.unique . coerced -- just the name coerced
                         DatatypeBind _ (Datatype _ _ _ n _) -> n ^. PLC.unique . coerced -- arbitrary: uses the match-function's unique as the principal unique of this data binding group

