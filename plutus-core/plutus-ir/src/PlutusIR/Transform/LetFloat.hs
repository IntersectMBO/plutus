{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}
module PlutusIR.Transform.LetFloat (floatTerm) where

import           PlutusIR
import           PlutusIR.Analysis.Dependencies
import           PlutusIR.MkPir                       hiding (error)
import           PlutusIR.Purity

import           Control.Lens                         hiding (Strict)
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.State

import qualified PlutusCore                           as PLC
import qualified PlutusCore.Constant                  as PLC
import qualified PlutusCore.Name                      as PLC

import qualified Algebra.Graph.AdjacencyMap           as AM
import qualified Algebra.Graph.AdjacencyMap.Algorithm as AM
import qualified Algebra.Graph.NonEmpty.AdjacencyMap  as AMN

import           Data.Either                          (fromRight)
import qualified Data.IntMap                          as IM
import qualified Data.Map                             as M
import qualified Data.Set                             as S
import qualified Data.Set.NonEmpty                    as NS

import qualified Data.List.NonEmpty                   as NE
import           Data.Maybe                           (catMaybes, mapMaybe)
import           Data.Semigroup.Foldable

{- Note [Float algorithm]
The goal of this PIR->PIR transformation is to float lets to their closest-surrounding lambda/Lambda abstraction or
let-effectful and potentially merge adjacent lets into let-groups for
better readability of the program's IR (and potentially reveal any later code optimizations).

Each let-binding is moved right underneath its closest-surrounding lambda/Lambda abstraction or let-effectful (or at toplevel in case of no surrounding lambdas/lets).
Afterwards, all let-bindings belonging to the same lambda/Lambda are merged into 1 or more let-groups. The ordering of
the generated let-groups under a lambda/Lambda is determined by the dependency-graph of the program's IR. The cardinality of the generated let-groups
is determined both by the order of already-generated let-groups of the same level (thus by the dependency-graph) and secondly by the lets' original recursivity
(we do not merge originally-recursive lets).

Note that we do not move (float) those let-bindings which are strict and their RHS is a non-value term. This is needed to preserve the denotational semantics of
the original PIR program, as can be seen in the wrong-floated counter-example:

original: let nonstrict x =
                let y = error in y
          in 1
=> wrongly-floated: let y = error
                 in let nonstrict x = y
                 in 1

Specifically the algorithm is done in two passes:


1st-pass: Traverses an IR term/program and for each let, marks the location of its closest-surrounding lambda or let-nonstrictvalue (or Top if no lambda),
and stores it into a mapping of let-name=>lambda/let-location. We call the closest-surrounding lambda/let-location the *Rank* of a let.
We have an extra pass that cleans a PIR term from all those lets that are *not* let-effectful; see Note [Cleaning lets].

2nd-pass: Traverses the cleaned-up term to place the removed lets back again, this time  directly under their "Rank".
During traversal, when a lambda-location of interest is reached (i.e. Rank),
the algorithm consults the dependency graph to figure (a) the groupings of lets
into let-groups based on their (mutual) recursivity (by utilizing the SCCs of the depgraph)
and (b) the correct code-generation *order* of the let-groups (by utilizing the topsort of the SCCs).
As an optimization, the algorithm merges adjacent *nonrec* let-groups into a single-group for better readability; this is possible
because letnonrec in PlutusIR is linearly scoped.

Example 1 (floating to the closest-surrounding lambda):

\ x -> 1 + (2 * let i = 3 in i+4)
==>
\ x -> let i = 3 in 1 + (2 * i+4)

Example 2 ( merging adjacent let-nonrecs):

\ x -> letnonrec nonstrict x = 1 in letnonrec nonstrict y = 2 in x + y
===>
\ x -> letnonrec nonstrict {x=1; y=2} in x + y


Invariants for the algorithm:

a) Does not float lets outside surrounding lambda/Lambda abstractions/let-effectful.
This has the effect of preserving the nonstrict/strict semantics of the original program.
b) Does not break scoping; only uses the `linear scoping` feature of let-nonrec  to merge adjacent letnonrecs
c) It will not demote a letrec to a letnonrec (however it may promote nonrec to rec as a consequence of rearranging lets)

About (c):
The algorithm may sometimes promote a nonrec to a rec; see for example `plutus-ir/test/transform/letFloat/nonrecToRec.golden`.
This is by design, in the way we use the dependency graph to create the let-groups; the dependency graph
may float upwards some nested let-rhses into an "outside" let-group, and this would require rec.
Example of `let-i` turning from nonrec to rec, by merging with the parent `r` group:

let rec r =
   let nonrec i =
        let nonrec j = r
        in j
   in i

==>

let rec {r = i
         i = let nonrec j = r
             in j
        }

Non-guarantees of the algorithm:

The algorithm does not guarantee that *fewer let-groups* will appear after the transformation,
see for example `plutus-ir/test/transform/letFloat/rec3.golden`. This can happen for two reasons:

i) The algorithm may split a recursive group into multiple groups when it sees that there are no dependencies between certain subgroups,
which is a side-effect of relying on the dependency-graph for determining the let-grouping
ii) The grouping may even be worsened by the "interleaving"/breaking of letnonrec and letrec groups;
the ordering of generated lets relies on *a* topological sort of the dependency graph. Since there can be many
topological sorts, there might exist a topological sort different than the one used,
which would otherwise yield less (or more) let groups.

-}

{- Note [Cleaning lets]
Prior to floating the lets of a term (i.e. pass2), we clean up the term from (almost) all its `let` constructs, and
store those separately in a LetUniqueId=>RhsTerm table (name RhsTable). This is done by the `removeLets` function.
The resulting "cleaned-up" term is most-likely not a valid PIR program anymore because it contains free variables.

The `let` constructs that are not cleaned-up, are the effectful ones:
these lets won't become keys of the output-RhsTable, and thus will not be floated during pass2.
This does not necessarily mean that these effectful-lets will appear in the output cleaned-up term;
they may appear inside the RHS values of the RhsTable (in case they are nested by a to-be-floated, "parent" let),
so their original "absolute" position may still change after pass2 because their parent-let has been floated somewhere else.
-}

-- | During the first-pass we compute the  "rank" for every let-binding declared in the given PIR program.
-- A rank points to a surrounding lambda/Lambda/let-effectful location which is closest to that let,
-- or Top if the let does not depend on any lambda/Lambda/leteffectful.
-- A rank can also be used as a pointer to a (lambda/Lambda/let) location in the PIR program.
data Rank =
  -- | Signifies that a let has no lambda/Lambda/let free dependency and thus can be placed at the toplevel of the program.
     Top
  -- | a let is directly surrounded by the lambda signified by the location lamDepth :: 'Int', lamUnique :: 'PLC.Unique'
  -- NB: the lamDepth (Int) should be strictly positive (1,2..)
     | Dep Int PLC.Unique
  deriving Eq

-- | Lens-style getter function for depth
-- NB: Top is arbitrarily defined as having depth 0.
-- It could also be made 'minBound' or 'Word', but this is conceptually clearer and allows us to use 'IM.IntMap's.
depth :: Getting r Rank Int
depth  = to $ \case
  Top     -> 0
  Dep d _ -> d

instance Ord Rank where
  compare Top Top                 = EQ
  compare Top _                   = LT
  compare _ Top                   = GT
  -- try depth, then try unique
  compare (Dep d1 u1) (Dep d2 u2) = compare d1 d2 <> compare u1 u2

-- | During the first pass of the AST, a reader context holds the closest-surrounding lambda of a term
type P1Ctx = Rank     --  the surround lambda (its location)


-- | During the first pass of the AST, we build an intermediate table to hold the ranks for the lets encountered so far.
-- This intermediate table will be transformed right at the end of 1st pass to 'FloatData'.
-- OPTIMIZE: We could use UniqueMap (a coerced IntMap) instead of `Map PLC.Unique`, but API is insufficient
type P1Data = M.Map
              PLC.Unique --  the "principal" identifier introduced by a let-binding. See Note [Principal]
              Rank --  its calculated rank

-- | Before we return from the 1st pass, we transform/view the accumulated 'P1Data'
-- to something that can be more easily consumed (by the second pass).
-- This 'FloatData' is another "view" of the 'P1Data', indexed/keyed by the "interesting" depths (Int) (depths to look for when floating in pass2).
-- Specifically, it is a mapping of depth=>lambda/Top/effectful=>{let_unique}.
-- We consume the float-data left-to-right, sorted on depth.
type FloatData = IM.IntMap ( --  the depth (starting from 0, which is Top)
                 M.Map --  a mapping of locations at this depth => to all letidentifiers to float at that depth.
                  Rank    --  the lam/Lam/leteffectful or Top location where the let should float to
                  (NS.NESet PLC.Unique) --  the let bindings that should be floated/placed under this location
                 )

-- | An Rhs of a let-binding is quadruple of Annotation, Recursivity, Binding expr(s), and its depth (location) in the original program.
--
-- The recursivity&Annotation is copied from the let-binding's group Recursivity&Annotation.
-- In other words the same Recursivity&Annotation is shared among the let-bindings that were belonging to the same let-group.
-- This sharing of the Recursivity is not optimal, because it may lead to more generated groups than the original program; however,
-- it is necessary so as to not wrongly demote any recursive lets to nonrecs. This let-floating transformation does not do
-- any demotion (letrec=>letnonrec) optimization; it is left to be implemented by another pass.
data Rhs tyname name uni fun ann = Rhs { _rhsAnn :: ann
                                   , _rhsRecurs  :: Recursivity
                                   , _rhsBinding :: Binding tyname name uni fun ann
                                   , _rhsRank    :: Int
                                   }
makeLenses ''Rhs

-- | First-pass: Traverses a Term to create the needed floating data:
-- a mapping of let variable to float inside the term ==> to its corresponding rank.
p1Term ::  forall name tyname uni fun a
    . (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique,
      PLC.ToBuiltinMeaning uni fun)
    => Term tyname name uni fun a
    -> FloatData
p1Term pir = toFloatData $ runReader
                           (goTerm pir)
                           Top -- the first "surrounding lambda" is the Top level
  where
    goTerm :: Term tyname name uni fun a -> Reader P1Ctx P1Data
    goTerm = \case
      -- update the surrounding lamdba/Lambda
      LamAbs _ n _ tBody  -> withAnchor (n^.PLC.theUnique) $ goTerm tBody
      TyAbs _ n _ tBody   -> withAnchor (n^.PLC.theUnique) $ goTerm tBody

      Let _ _ bs tIn    -> do
        resBs <- mconcat <$> forM (NE.toList bs) goBinding
        resIn <- goTerm tIn
        pure $ resBs <> resIn

      -- recurse and then accumulate the return values
      t -> mconcat <$> traverse goTerm (t^..termSubterms)

    goBinding :: Binding tyname name uni fun a -> Reader P1Ctx P1Data
    goBinding b =
      let subtermRanks = mconcat <$> traverse goTerm (b^..bindingSubterms)
      in if mayHaveEffects b
         -- leteffectful bindings are anchors themselves like lam/Lam/Top
         then withAnchor (b^.principal) subtermRanks
         -- for all other let bindings we record their ranks
         else (<>) <$> addRank b <*> subtermRanks

    -- | Given a binding, return new data ('P1Data') by inserting mapping of principal let-identifier
    -- to this maximum rank (taken from the "enclosing" environment)
    addRank :: Binding tyname name uni fun a -- ^ bindings
             -> Reader P1Ctx P1Data -- ^ the updated scope that includes the added ranks
    addRank b = do
      anchorUp <- ask
      pure $ M.singleton (b^.principal) anchorUp

    -- | Transform the 1st-pass accumulated data to something that is easier to be consumed by the 2nd pass (that does the actual floating).
    toFloatData :: P1Data -> FloatData
    toFloatData = M.foldrWithKey fromP1Value IM.empty
      where
        fromP1Value :: PLC.Unique -- ^ the principal identifier of the let gathered to float later
                    -> Rank -- ^ a p1-entry is its computed maximum rank (surrounding anchor)
                    -> FloatData          -- ^ the acc new structure
                    -> FloatData
        fromP1Value letPrincipal anchor = IM.insertWith
          -- the combinining function of "ground values": combining the anchor-maps of the same depth
          (M.unionWith (<>))
          -- use the depth for the key of the new depthmap (intmap)
          (anchor^.depth) -- the depth of the anchor (lam/Lam/leteffectful/Top)
          -- "the ground value" inserted in the intmap, is a singleton "anchormap" of anchor
          -- mapped to the principal unique of the let-to-be-floated
          (M.singleton anchor $ NS.singleton letPrincipal)

    -- | Updates the closest-surrounding lam/Lam/leteffectful location for some `b` computation
    withAnchor :: PLC.Unique -> Reader P1Ctx b -> Reader P1Ctx b
    withAnchor u = local $ \oldAnchor  ->
                             let newDepth = oldAnchor^.depth + 1
                                 newAnchor = Dep newDepth u
                             in newAnchor


-- To make the 2nd pass easier, we prior "clean" the PIR term from most let declarations and store them separataly in a 'RhsTable'.
-- The lets we don't clean are leteffectful bindings.
-- The 2nd pass will later place all these table entries back inside the cleaned term, thus "floating" those lets.

-- | A simple table holding a let-introduced identifier/unique to its RHS.
--
-- In case of a datatype-let (which has multiple identifiers&bindings), we add a table entry for each identifier of that datatype.
-- The multi-let-grouppings of the initial PIR program do not exist anymore in this representation.
-- OPTIMIZE: We could use UniqueMap (a coerced IntMap) instead of `Map PLC.Unique`, but API is insufficient
type RhsTable tyname name uni fun a = M.Map
                                  PLC.Unique
                                  (Rhs tyname name uni fun a)



-- | This function takes a 'Term', cleans the 'Term' from most of its 'Let'-bindings and
-- stores those lets into a separate table.See Note [Cleaning lets]
-- OPTIMIZE: this traversal may potentially be included/combined with the 1st-pass.
removeLets
    :: forall name tyname uni fun a
    . (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique,
      PLC.ToBuiltinMeaning uni fun)
    => Term tyname name uni fun a
    -> (Term tyname name uni fun a, RhsTable tyname name uni fun a)
removeLets t =
  runState
    -- keep track of the current depth, while we are searching for lets, starting from Top depth = 0
    (runReaderT (go t) $ Top^.depth)
    -- initial table is empty
    mempty
 where
   go :: (MonadReader Int m, MonadState (RhsTable tyname name uni fun a) m) => Term tyname name uni fun a -> m (Term tyname name uni fun a)
   go = \case
         -- this overrides the 'termSubterms' functionality only for the 'Let' constructor
         LamAbs a n ty tBody -> LamAbs a n ty <$> local (+1) (go tBody)
         TyAbs a n k tBody  -> TyAbs a n k <$> local (+1) (go tBody)

         Let a r bs tIn -> do
          curDepth <- ask
          bs' <- forM bs $ \b -> do
            b' <- b & bindingSubterms go
            if mayHaveEffects b
            then pure $ Just b' -- keep this let
            else do
              -- remove the let and store it in the rhstable
              modify . M.insert (b'^.principal) $ Rhs { _rhsAnn = a
                                                      , _rhsRecurs = r
                                                      , _rhsBinding =  b'
                                                      , _rhsRank = curDepth
                                                      }
              pure Nothing
          let nbs' = catMaybes $ NE.toList bs'
          mkLet a r nbs' <$> go tIn

         t' -> t' & termSubterms go

-- | Starts the 2nd pass from the 'Top' depth and the toplevel expression of the cleanedup term (devoid of any lets).
p2Term :: forall name tyname uni fun a .
       (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique, Semigroup a,
       PLC.ToBuiltinMeaning uni fun)
       => Term tyname name uni fun a
       -> FloatData
       -> Term tyname name uni fun a
p2Term pir fd =
  -- the 2nd pass starts by trying to float any lets around the top-level expression (body)
  -- For optimization reasons, we keep a state of remaining SCCs that we need to scan when we are generating let-groups in their correct order.
  -- The initial state starts from the all sccs top.sorted; IMPORTANT: the invariant is that the sccs in the state should always remain top.sorted.
  case runState (goFloat Top fd pirClean) topSortedSccs of
    (res, []) -> res
    -- note to self: the following error-detection requires that all lambdas and effectful lets are prior stripped-off from the `topSortedSccs`
    (_, remState) -> error $ "The final term is missing some lets because of a problem. The lets that could not be floated back to the final term were:" ++ show remState

 where
  -- | Prior to starting the second pass, we clean the term from all its let-declarations and store them separately in a table.
  -- The 2nd pass will later re-introduce these let-declarations, potentially placing them differently than before, thus essentially "floating the lets".
  (pirClean :: Term tyname name uni fun a, rhsTable :: RhsTable tyname name uni fun a) = removeLets pir

  -- 2nd-pass functions
  ---------------------

  -- | visit each term to apply the float transformation
  goTerm :: Int -- ^ current depth
         -> FloatData -- ^ the lambdas we are searching for (to float some lets inside them)
         -> Term tyname name uni fun a
         -> State [NS.NESet PLC.Unique] (Term tyname name uni fun a)
  goTerm curDepth floatData t = do
    curState <- get
    case curState of
      [] -> pure t -- floating-state is empty, stop descending to the term
      _ -> case t of
        -- we are only interested in lambdas/Lambdas
        LamAbs a n ty tBody -> LamAbs a n ty  <$> incrDepth curDepth n floatData tBody
        TyAbs a n k tBody  -> TyAbs a n k <$> incrDepth curDepth n floatData tBody
        -- these are the effectful-lets that are not floated
        Let a r bs inTerm ->
          -- here we have an opportunity to merge the "fixed" effectful-let iff its in-term is a nonrec let
          letMergeOrWrap a r
          -- increase the depth in the RHS of each binding. the effectful-lets are thus anchors (like lambdas/Lambdas)
          <$> forM bs (\b -> b & bindingSubterms (incrDepth curDepth (b^.principal) floatData))
          --  the inTerm has not increased-depth
          <*> goTerm curDepth floatData inTerm

          -- descend otherwise to apply the transformations to subterms
        t' -> t' & termSubterms (goTerm curDepth floatData)

  -- | If a lambda/Lambda/LetEffectful is found, the current location is updated (depth+Unique) and try to float in its body/RHS
  incrDepth :: PLC.HasUnique b b'
            => Int -- ^ current depth
            -> b                  -- ^ lambda/Lambda's/LetEffectful unique
            -> FloatData -- ^ the lambdas we are searching for (to float some lets inside them)
            -> Term tyname name uni fun a -- ^ lambda/Lambda's/Let body
            -> State [NS.NESet PLC.Unique] (Term tyname name uni fun a)
  incrDepth oldDepth n = let newDep = Dep (oldDepth+1) (n^.PLC.theUnique)
                         in goFloat newDep

  -- | We are currently INSIDE (exactly under) a lambda/Lambda body/Top (Top if we are right at the start of the algorithm)
  -- We try to see if we have some lets to float here based on our 1st-pass-table data (searchTable).
  goFloat :: Rank -- ^ the rank/location of the lambda/letEffectful above that has this body
          -> FloatData -- ^ the lambdas we are searching for (to float some lets inside them)
          -> Term tyname name uni fun a                           -- ^ the body term
          -> State [NS.NESet PLC.Unique] (Term tyname name uni fun a) -- ^ the transformed body term
  goFloat curAnchor floatData tBody =
   -- look for the next smallest depth remaining to place
   case IM.minViewWithKey floatData of
     Nothing -> pure tBody -- nothing left to float
     Just ((searchingForDepth, searchingForAnchor_Lets), restFloatData) ->
      let curDepth = curAnchor^.depth
      in case curDepth `compare` searchingForDepth of
        -- the minimum next depth we are looking for, is not this one, so just descend with the whole floatdata
        LT -> goTerm curDepth floatData tBody
        -- found depth, see if our lambda above is a lambda we are interested in (to float some lets)
        EQ -> genLets (M.lookup curAnchor searchingForAnchor_Lets)
                   restFloatData
                   <*> goTerm curDepth restFloatData tBody
        GT -> error "This shouldn't happen, because the algorithm takes care to stop descending when EQ is reached."


  -- | the dependency graph (as the one used by the deadcode elimination)
  -- but w/o the root node and only uses the Var's Unique as the node id
  -- OPTIMIZE: we could use AdjacencyIntMap, but then we require the UniqueMap optimizations, and we lose the type-safety of newtype Unique
  depGraph :: AM.AdjacencyMap PLC.Unique
  depGraph = AM.induceJust .
             AM.gmap (\case Variable u -> Just u;
                            -- we remove Root because we do not care about it
                            Root       -> Nothing)
             $ fst $ runTermDeps pir

  -- | the dependency graph as before, but with datatype-bind nodes merged/reduced under the "principal" node, See Note [Principal].
  reducedDepGraph :: AM.AdjacencyMap PLC.Unique
  reducedDepGraph = M.foldr maybeMergeNode depGraph rhsTable
    where
      maybeMergeNode :: Rhs tyname name uni fun a -> AM.AdjacencyMap PLC.Unique -> AM.AdjacencyMap PLC.Unique
      maybeMergeNode rhs = let ids = rhs^..rhsBinding.bindingIds
                           in case ids of
                               -- A lot of binds are termbinds/typebinds with no vertices to merge.
                               -- This optimizes all these cases of termbinds/typebinds to avoid traversing in O(n) the graph
                               -- looking for "possible" merges, because there are none to be performed
                               [_nonDatatypeBind] -> id -- retain the accgraph
                               _   ->  AM.mergeVertices (`S.member` S.fromList ids) (rhs^.rhsBinding.principal)

  -- |take the strongly-connected components of the reduced dep graph, because it may contain loops (introduced by the LetRecs)
  -- topologically sort these sccs, since we rely on linear (sorted) scoping in our 'genLets' code generation
  topSortedSccs :: [NS.NESet PLC.Unique]
  topSortedSccs =
    let allLets = M.keysSet rhsTable
    in mapMaybe (\scc ->  NS.nonEmptySet $
                  -- we are not interested in graph structure anymore
                  -- make sure that scc contain only to-be floated lets (i.e. no lambdas and no fixed effectful lets)
                  AMN.vertexSet scc `S.intersection` allLets
                )
       . fromRight (error "Cycle detected in the scc-graph. This shouldn't happen in the first place.") . AM.topSort $ AM.scc reducedDepGraph

  -- | Groups a given set of lets into one or more multilets and wraps these multilets around a term.
  -- The grouping is done through the strongly-connected components
  -- The input lets are not sorted w.r.t. linear scoping, so this function uses the topological-sort of these SCCs,
  -- to figure out the correct (dependent/linear) order in which to generate these new multilets.
  --
  -- The resulting term is wrapped with linear-scope-sorted LetRecs and LetNonRecs (interspersed between each other because letnonrec and letrec syntax cannot be combined)
  -- Example: `let {i = e, ...} in let rec {j = e, ...} in let rec {...} in let {...} in ..... in originalTerm`
  genLets :: Maybe (NS.NESet PLC.Unique) -- ^ all the let identifiers to wrap around this term
          -> FloatData -- ^ the remaining data to be floated
          -> State [NS.NESet PLC.Unique] (Term tyname name uni fun a -> Term tyname name uni fun a) -- ^ a wrapper function of term
  genLets Nothing _ = pure id -- nothing to float, return just the term
  genLets (Just lets) restDepthTable = do
    (hereSccs, restSccs) <- gets $ splitSccs lets
    put restSccs
    foldM genLetsFromScc id hereSccs
      where
        -- | given an SCC, it creates a new (rec or nonrec) let-group from it and wraps it around an accumulated term
        -- Special case: if the new group and the accumulated term are both letnonrecs,
        -- it merges them together into a single let-group (i.e. linear scoped).
        genLetsFromScc :: (Term tyname name uni fun a -> Term tyname name uni fun a)
                       -> NS.NESet PLC.Unique
                       -> State [NS.NESet PLC.Unique] (Term tyname name uni fun a -> Term tyname name uni fun a)
        genLetsFromScc accTerm scc = do
              visitedRhses <- forM (NS.toList scc) $ \v ->
                 case M.lookup v rhsTable of
                   Just rhs ->
                     let oldDepth = rhs^.rhsRank
                     in -- visit the generated rhs-term as well for any potential floating
                       rhs & (rhsBinding.bindingSubterms)
                       (goTerm
                         -- inside the RHS we "pretend" that we are at the depth of the let in the original program,
                         -- since the depths of lets in FloatData correspond to the original depths.
                         oldDepth
                         -- for optimization, we pass only a part of the floatdata that are larger than this RHS orig. depth.
                         (snd $ IM.split oldDepth restDepthTable))
                   _ -> error "Something went wrong: no rhs was found for this let in the rhstable."

              let (newAnn, newRecurs, newBindings) = foldMap1 rhsToTriple visitedRhses -- fold the triples using <>
              pure $ letMergeOrWrap newAnn newRecurs newBindings . accTerm -- wrap the ACCumulator-wrapper function

           where
             rhsToTriple :: Rhs tyname name uni fun a
                         -> (a, Recursivity, NE.NonEmpty (Binding tyname name uni fun a))
             rhsToTriple rhs =
                      (rhs^.rhsAnn
                       -- if the SCC is a single node then use its original 'Recursivity';
                       -- otherwise, the SCC is  a group of nodes and we *have to* treat all of them in a 'letrec',
                       -- since we don't have any information on how to linearize those.
                      , if isSingleton scc then rhs^.rhsRecurs else Rec
                       -- lift the binding into a semigroup for accumulation
                      , pure $ rhs^.rhsBinding)



-- | Tries to merge a new let-triple (ann,recursivity,bindings) with a next in-term
-- iff the  let is nonrec and the next in-term is also a let-nonrec. Otherwise,
-- it generates (wraps) the new-let around the in-term.
letMergeOrWrap :: Semigroup a
               => a -- ^ the new-let ann
               -> Recursivity -- ^ the new-let recurs
               -> NE.NonEmpty (Binding tyname name uni fun a) -- ^ the new-let bindings
               -> Term tyname name uni fun a                  -- ^ the term t1 to merge with or to wrap it around `let newlet {bs} in {t1}`
               -> Term tyname name uni fun a                  -- ^ the final merged or wrapped term
letMergeOrWrap newAnn newRecurs newBindings = \case
  -- MERGE current let-group with previous let-group iff both groups' recursivity is NonRec
  Let nextAnn NonRec nextBs nextIn | newRecurs == NonRec -> Let (newAnn <> nextAnn) NonRec (newBindings <> nextBs) nextIn
  -- never merge if the previous let-group is a Rec or the current let-group is Rec,
  -- but instead create a nested current let-group under the previous let-group (above)
  t -> Let newAnn newRecurs newBindings t


-- | The main transformation function (Term -> Term) to "float" all lets of a term under their closest-surrounding lambda/Lambda.
-- Is comprised of two AST "passes":
-- 1stpass: to collect the ranks (future positions) of all lets
-- 2ndpass:  to remove all its lets and place them back (float them) to their ranks (new positions).
-- See Note [Float algorithm]
--
-- NB: This transformation requires that the PLC.rename compiler-pass has prior been run.
floatTerm :: forall name tyname uni fun a.
          (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique, Semigroup a,
           PLC.ToBuiltinMeaning uni fun)
          => Term tyname name uni fun a -> Term tyname name uni fun a
floatTerm pir = p2Term pir
                -- give the floatdata of the 1st pass to the start of the 2nd pass
              $ p1Term pir



-- Helpers
----------

-- | A getter that returns a single 'Unique' for a particular binding.
-- We need this because let-datatypes introduce multiple identifiers, but in our 'RhsTable', we use a single Unique as the key.
-- See Note [Principal]. See also: 'bindingIds'.
principal :: (PLC.HasUnique tyname PLC.TypeUnique, PLC.HasUnique name PLC.TermUnique)
            => Getting r (Binding tyname name uni fun a) PLC.Unique
principal = to $ \case TermBind _ _ (VarDecl _ n _) _                            -> n ^. PLC.theUnique
                       TypeBind _ (TyVarDecl _ n _) _                            -> n ^. PLC.theUnique
                       -- arbitrary: uses the type construtors' unique as the principal unique of this data binding group
                       DatatypeBind _ (Datatype _ (TyVarDecl _ tConstr _) _ _ _) -> tConstr ^. PLC.theUnique


-- | During pass2, whenever we find an anchor (lambda/Lambda or letEffectful) we try to float
-- those lets (`ls`) that are dictated by the FloatData of pass1.
-- For performance, the pass2  keeps a State of [SCC PLC.Unique], which contain the lets
-- as vertices that we haven't floated back yet. These vertices are either lets to be floated back
-- eventually or lambda/Lambda/letEffectful (that we didn't strip off from the dependency-SCC graph).
-- 1) sccs to process at this location
-- 2) and remainder sccs to use as the next state.
splitSccs :: Ord a
          => NS.NESet a -- ^ The lets determine the split of sccs.
          -> [NS.NESet a] -- ^ the sccs to split
          -> ( [NS.NESet a] -- the first part of the split, which will be floated now, at the current iteration of the pass2
            , [NS.NESet a] -- the second part of the split, the "remaining sccs" which will be put back into the state to be processed later by pass2
            )
splitSccs _ [] = ([],[]) -- reached end of sccs, done splitting
splitSccs lets (scc:sccs) =
   let
       -- The sub-scc we are interested in floating right now, at this iteration of pass2
       commonScc = scc `NS.intersection` lets
       -- The sub-scc we have to put back to the pass2's state (to-be-floated later)
       remainingScc = NS.toSet scc S.\\ commonScc
       -- For performance of subsequent splitting, we take the remainingLets for the next recursion.
       -- Lets that were not accounted for in this scc, but may appear in the tail `sccs` when recursing `splitSccs`
       remainingLets = NS.toSet lets S.\\ commonScc
       -- recurse with the tail sccs
       (commonSccs,remainingSccs) = case remainingLets of
                       -- visit the tail sccs to split based on the non-empty remaininglets
                       NS.IsNonEmpty neRemainingLets -> splitSccs neRemainingLets sccs
                       -- No lets are left to process, stop splitting
                       _                             -> ([], sccs)
   -- Note to self: after processing an scc, we place back its remainder. This is not necessary anymore
   -- in this new iteration of the algorithm and since we prior strip the lambdas/letnonstrictvalues
   -- it is needed however if we float differently with the old iteration of algorithm that used freevar counting
   in ( commonScc ?: commonSccs
      , remainingScc ?: remainingSccs
      )
  where
    -- CONS operator that skips consing empty-sets in the front
    (?:) :: S.Set a -> [NS.NESet a] -> [NS.NESet a]
    NS.IsNonEmpty n ?: l = n:l
    _ ?: l               = l -- id otherwise

-- | Returns if a foldable can be folded in 1 iteration, hence its length is 1.
isSingleton :: NS.NESet a -> Bool
isSingleton s = NS.size s == 1

-- | Returns if a binding's rhs is strict and may have effects (see Value.hs)
mayHaveEffects
    :: PLC.ToBuiltinMeaning uni fun
    => Binding tyname name uni fun a
    -> Bool
-- See Note [Purity, strictness, and variables]
-- We could maybe do better here, but not worth it at the moment
mayHaveEffects (TermBind _ Strict _ t') = not $ isPure (const NonStrict) t'
mayHaveEffects _                        = False

{- Note [Versus the "Let-floating"-paper]

Reference: Peyton Jones, Simon, Will Partain, and Andre Santos. "Let-Floating: Moving Bindings to Give Faster Programs."
In Proceedings of the First ACM SIGPLAN International Conference on Functional Programming, 1-12.
ICFP '96. New York, NY, USA: ACM, 1996. https://doi.org/10.1145/232627.232630.

The algorithm of the paper deals with a different source language (Haskell/GHC),
which only has 'letrec' and no support for letnonrec, type-lets, and datatype-lets.

The paper's algorithm can be summarized to:

* The first pass of the term annotates all let-bindings with their ranks (level numbers).
The algorithm collects all the variables that occur free in a let's RHS and their ranks
which were calculated before, at the place where those free variables were defined. The let
is assigned the maximum of those ranks.
* The second pass of the term uses those ranks "to float each binding outward to just
outside the lambda which has a rank (level number) one greater than that on the binding".

## Difference 1 - Rank

For our case, a rank of a let is its closest-surrounding lambda "location" (depth + unique).
In the paper, a rank of a let is calculated as the maximum among the ranks
of the free-variable dependencies that occur in the let's RHS; a rank of a lambda is just its lambda-depth.
The paper's rank includes only the lambda depth and not the lambda-unique.
This is because the lambda-uniques are not needed by the original second pass because
the re-positions of lets are applied "locally" (see Difference - Algorithm).

## Difference - Algorithm

The paper's algorithm applies the float-transformations "locally":
during the second pass, when a let is encountered the algorithm will "decide" at that point to float it outwards or inwards.
This allows more flexibility (heuristics and the possibility to float inwards).

We use a different approach where we prior clean the AST PlutusIR term from all the lets (rec&nonrec)
and store them in a separate 'RhsTable' (see `removeLets` function). We use the information obtained by the dependency graph
to create let-(rec&nonrec) groups at the closest-surrounding lambda location (rank). During
the second pass, whenever we reach a lambda/Lambda definition we float all lets belonging to
this lambda rank (i.e. lambda's depth and unique).
This means that the lets are floated *exactly under* a lambda definition, i.e at the lambda body.

Contrast this with the paper's algorithm, where
lets are floated exactly around the 'expr' that
needs them, and *exactly outside a lambda definition*.
This is because the algorithm stops re-positioning / floating the let-rhs, when it crosses over a lambda with depth
one larger than its calculated rank (level number). Thus, for every lambda rank, a single merged let-group may be generated;
this is no problem for Haskell/GHC, because all lets are letrecs.
The advantage compared to our approach is that the lets will be floated closer to the 'expr' that needs them.
Unfortunately, we cannot use this algorithm in our case for 2 reasons:  a) we cannot float past lambdas/letEffectful because
the language features strict lets and floating would alter the denotational semantics  and b)
in each rank we possibly need to generate multiple let-groups because we have to intersperse between letrecs and letnonrecs.
-}

{- Note [Principal]
In a few structures (the rhstable, the p1data, and the floatdata) we use as a key the unique identifier of a let to store information,
such as the computed rank or the RHS of a let. Since a datatypebind contains multiple declarations, each with its
own identifier (unique), we arbitrarily use one of those (the "principal" identifier) as the index/key for our structures.
This is allowed because the datatypebind declarations of a datatypebind (identifiers) share the same rank and will
"float" altogether as one.

In a previous iteration of the algorithm that used FREE-VARIABLE counting, the "principal" played an extra role:
the intermediate 'p1data' had mappings of each databind declaration's unique to the datatype bind's maximum rank.
e.g. if a datatypebind List had maximum rank `Top`, we added entries List=>Top, a=>Top, Nil=>Top, Cons=>Top.
This was needed because the 'p1data' acted also as a **scope**, so other lets can compute their maximum ranks by looking up their free variables
in the scope -- they couldn't know that an identifier was belonging to what group of identifiers (datatypebind).
At the end of p1, the p1data was transformed to floatdata by removing extraneous datatypebind entries, thus only keeping
the principal identifier entry, as is in the current iteration of the algorithm.
-}
