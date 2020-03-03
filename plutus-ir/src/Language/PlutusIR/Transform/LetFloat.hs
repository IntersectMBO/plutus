{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
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
import           Data.Function                           (on)
import qualified Data.IntMap                             as IM
import qualified Data.Map                                as M
import           Data.Maybe                              (fromMaybe)
import qualified Data.Set                                as S

{- Note: [Float algorithm]

Our algorithm is influenced by the algorithm described in Section-4 of:
Peyton Jones, Simon, Will Partain, and Andre Santos. "Let-Floating: Moving Bindings to Give Faster Programs." In Proceedings of the First ACM SIGPLAN International Conference on Functional Programming, 1-12. ICFP '96. New York, NY, USA: ACM, 1996. https://doi.org/10.1145/232627.232630.

Our algorithm tries to do two things:

a) move let-bindings as outwards as possible (a.k.a. full laziness).
b) merge any floated,let-NonRec bindings which are adjacent, into a multi-let group (for readability purposes).

Our algorithm is comprised of two passes of the PlutusIR AST:

- 1st pass: Compute the "maximum ranks" of all lets in a given term. A maximum rank signifies a source-code position that the let will be moved/floated to during the 2nd pass.
- 2nd pass: Move lets to their maximum rank positions. The pass makes sure that same-rank lets are grouped in multi-let-groups which
are topologically sorted by their dependency graph (see 'Dependencies.runTermDeps').

-}

{- Note: [Float first-pass]

Visits a PIR term and marks all identifiers introduced by lets with their "maximum rank" (level number in the paper).

A maximum rank of a let-bound identifier can be seen as its "deepest" (lambda,Lamdba,or let)-dependency that occurs free in that let's RHS.

The depth of a lambda/Lambda-dependency that occurs free in the RHS, is calculated as: the number of lambdas that surround this lambda/Lambda + 1.
The depth of a let-dependency that occurs free in the RHS, is the depth of the "maximum rank" calculated for that let-dependency.

Any dependencies that are bound inside the rhs are simply ignored.

In the special case of a letrec group, every let of that group is assigned the maximum (deepest) rank among all lets.

The first-pass returns a mapping of maximum-ranks to let-identifiers, sorted on depth (see 'FloatData').

-}

{- Note: [Float second-pass]

The second-pass first cleans the input ASTs of all let-rhs'es and puts them in a separate table 'RhsTable'.
(actually this is yet another pass, but we don't count this cleaning pass as an individual pass, to match the pass-numbering of the original algorithm).

The second pass then traverses the 'cleaned term', and whenever it reaches a lambda/Lambda position (Rank) which exists as key in the 'FloatData' table,
it floats its corresponding lets directly inside the lambda/Lambda's body.
The introduced lets of each Rank (level number) are not grouped in a single multi-let-rec group (as in the original algorithm), but instead in possible-multiple
let-(nonrec & rec) groups. This groupping is done in accordance with the dependency-graph (see 'runTermDeps'):
any let group that depends on a prior let-(rec or nonrec) group, will appear nested inside that group. The algorithm merges adjacent let-nonrec groups
into a single let-nonrec group, since the letnonrec is linearly scoped: `(let {i=...j=...} in...) === (let i=... in let j=... in ...)`.

By design choice, the second-pass preserves the floated let-bindings' original (Rec and NonRec) recursivity labels;
it will never demote a 'Rec' let-binding to a 'NonRec', despite the demotion being valid.
The effect is that more let-groups may be generated in a specific Rank than it would otherwise be required (optimally).
The demotion can potentially be a nice optimization/transformation, but the way the depenndency-graph is generated for datatype binds, makes this complicated.
See test example: `plutus-ir/test/transform/letFloat/rec3.golden`

-}

{- Note: [Versus original algorithm]

Note that the original algorithm is applied to a different source language (Haskell/GHC), which only has 'letrec' and no support for letnonrec, type-synonym-lets, and datatype-lets.

The original algorithm of that paper can be summarized to:

1. The first pass of the term annotates all let-bindings with their ranks (level numbers). A rank is the maximum depth of a free-variable dependency.
2. The second pass of the term uses those ranks "to float each binding outward to just outside the lambda which has a rank (level number) one greater than that on the binding".


A rank in the original paper includes only the lambda depth and not the lambda-name. This is because the lambda-names are not needed by the original second pass because
the re-positions of lets are applied "locally" (versus globally in our case, more on that later).

The first-pass remains more or less the same.

The second pass is heavily altered. The original algorithm's second pass applies "local transformations": when it stumbles upon a let, it looks up its rank
and "locally" decides if it is worth to float the let-rhs (outwards based on its rank or even inwards). It stops re-positioning / floating outwards the let-rhs,
when it crosses over a lambda with depth one larger than its rank (level number).
The advantage is that the lets will be floated exactly around the 'expr' that needs them, and *exactly outside a lambda definition*.
The downside is that there is a single merged let-group geneerated in every rank. This is no problem for Haskell/GHC, because lets are letrecs.

We use a different approach where we prior clean the AST PlutusIR term from all the lets (rec&nonrec) and store them in a separate 'RhsTable'.
We use the information obtained by the dependency graph to create let-(rec&nonrec) groups at that rank. A rank is a lambda depth plus a lambda name. During
the second pass, whenever we reach a lambda/Lambda definition we float all lets beloning to this lambda (rank, i.e. lambda's depth and name).
This means that the lets are floated *exactly inside a lambda definition, i.e at the lambda body*, with the downside being that they are floated "a bit" more outside than what would
be optimal as in the original algorithm (floated exactly around the 'expr' that needs them, and *exactly outside a lambda definition*).
The upside is that this approach is not local/ad-hoc, but more holistic.

-}


-- | During the first-pass we compute a maximum "rank" for every let-binding declared in the given PIR program.
-- See Note: [Float first-pass]
-- A rank points to either a lambda/Lambda location or Top if the let does not depend on any lambda/Lambda.
-- A "maximum rank" is the 'Rank' with the largest depth, i.e. the deepest lambda-dependency.
-- A rank can also be used as a pointer to a (lambda) location in the PIR program.
data Rank = Top -- ^ signifies that a let has no lambda/Lambda dependency and thus can be placed at the toplevel of the program
          | LamDep Int PLC.Unique -- ^ a let has a lambda/Lambda dependency with lamDepth :: 'Int', lamName :: 'PLC.Unique'
          deriving Eq

-- | The underlying classic getter function for depth
--
-- Note: Top is arbitrarily defined as having depth 0.
-- It could also be made 'minBound' or 'Word', but this is conceptually clearer and allows us to use 'IM.IntMap's.
_depth :: Rank -> Int
_depth = \case
  Top -> 0
  LamDep d _ -> d

-- | Lens-style getter of the depth of a rank
depth :: Getting r Rank Int
depth  = to _depth

instance Ord Rank where
  compare = compare `on` _depth

-- | We are interested in maximal ranks, and thus we use Rank similar to 'Data.Semigroup.Max'.
-- OPTIMIZE: we could get rid of the following Semigroup and Monoid instances by wrapping with 'Data.Semigroup.Max'.
instance Semigroup Rank where
  r1 <> r2 = max r1 r2

-- | The minimum rank is Top (toplevel/ no lambda/Lambda dependency).
instance Monoid Rank where
  mempty = Top

-- | During the first pass of the AST, a reader context holds the current in-scope lambda locations (as Ranks).
type P1Ctx = ( P1Data  --  the lambdas-in-scope that surround an expression
             , Int     --  the current depth
             )


-- | During the first pass of the AST, we build an intermediate table to hold the maximum ranks of each let encountered so far.
-- This intermediate table will be transformed right at the end of 1st pass to 'FloatData'.
type P1Data = M.Map
              PLC.Unique --  the identifier introduced by a let-binding
              ( Rank --  its calculated maximum rank, i.e. where this identifier can topmost/highest float outwards to
              , PLC.Unique   --  a principal name for this binding (needed specifically because a let-Datatype-bind can introduce multiple identifiers)
              )

-- | Before we return from the 1st pass, we transform the acccumulated 'P1Data' to something that can be more easily consumed (by the second pass).
-- This 'FloatData' is a mapping of depth=>lambda=>{let_unique}. We consume the float-data left-to-right, sorted on depth.
--
-- TODO: This could instead use an 'IM.IntMap', to guarantee that the consumption is in the ordering of depth. However there was a bug when using the 'IM.minViewWithKey'
type FloatData = [(Int, --  the depth (starting from 0, which is Top)
                 M.Map --  a mapping of lambda-locations at this depth => to all letidentifiers to float at that depth.
                  Rank    --  the location where the let should float to: location is a lambda name or Top
                  (S.Set PLC.Unique) --  the let bindings that should be floated/placed under this lambda or Top
                 )]

-- | First-pass: Traverses a Term to create a mapping of every let variable inside the term ==> to its corresponding maximum rank.
p1Term ::  forall name tyname uni a
        . (Ord (tyname a), PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
        => Term tyname name uni a -> FloatData
p1Term pir = toFloatData $ runReader
                           (goTerm pir)
                           (M.empty, Top^.depth) -- starting from toplevel depth: 0
  where
    goTerm :: Term tyname name uni a
        -> Reader P1Ctx P1Data
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
      _ -> asks fst -- the ctx's p1data is propagated back outwards as the return value

    goBody :: PLC.HasUnique b b' => b -> Term tyname name uni a -> Reader P1Ctx P1Data
    goBody n tBody =
      let lamName= n^.PLC.unique.coerced
      in M.delete lamName -- this trick removes any lamrank from the final value, since we don't care about lambdas in the final pass1 result (P1Data)
         <$> (local (\ (scope,oldDepth) ->
                        let newDepth = oldDepth+1
                            newRank = LamDep newDepth lamName
                            newScope = M.insert lamName (newRank,lamName) scope -- adds a new lam rank to the current scope
                        in (newScope, newDepth))
                    $ goTerm tBody)

    goRec :: [Binding tyname name uni a] -> Term tyname name uni a -> Reader P1Ctx P1Data
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

    goNonRec :: [Binding tyname name uni a] -> Term tyname name uni a -> Reader P1Ctx P1Data
    goNonRec bs tIn =
      foldr (\ b acc -> do
           -- this means that we see each binding individually, not at the whole let level
           let freeVars = fBinding b
           -- compute a maxrank for this binding alone and a newscope that includes it
           newScope <- addRanks [b] freeVars
           resHead <- mconcat <$> forM (b^..bindingSubterms) goTerm
           resRest <- withScope newScope acc
           pure $ resHead <> resRest
       ) (goTerm tIn) bs


    -- | Given a set of bindings and the union set of their free-variables,
    -- compute the maximum 'Rank' among all the free-variables,
    -- and increase the current scope ('P1Data') by inserting mappings of each new let-identifier to this maximum rank
    addRanks :: [Binding tyname name uni a] -- ^ bindings
             -> S.Set PLC.Unique -- ^ their free-vars
             -> Reader P1Ctx P1Data -- ^ the updated scope that includes the added ranks
    addRanks bs freeVars = do
      (scope, _) <- ask
      let
          -- the ranks of the free variables
          freeRanks = fmap fst $ M.restrictKeys scope freeVars
          -- the max rank from all their free variables
          maxRank = fold freeRanks
          -- this computed max rank is linked/associated to all the given bindings and added to the current scope
          newScope = foldr (\ b acc ->
                               -- this fold is needed because a datatype-binding may introduce multiple identifiers
                               -- and we need to create scope entries for each one of them, having the same maxrank
                               foldr (\i ->  M.insert i (maxRank, b^.principal)) acc $ bindingIds b
                           ) scope bs
      pure newScope


    withScope :: P1Data -> Reader P1Ctx b -> Reader P1Ctx b
    withScope s = local (set _1 s) -- changes only the scope (i.e. p1data in our case)


    -- | Transform the 1st-pass accumulated data to something that is easier to be consumed by the 2nd pass (that does the actual floating).
    toFloatData :: P1Data -> FloatData
    toFloatData = IM.toAscList . foldr (\ (dep, letNamePrinc) acc -> IM.insertWith (M.unionWith (<>)) (dep^.depth) (M.singleton dep (S.singleton letNamePrinc)) acc) IM.empty



-- To make the 2nd pass easier, we prior "clean" the PIR term from all its let declarations and store them separataly in a 'RhsTable'.
-- The 2nd pass will later place all these table entries back inside the cleaned term, thus "floating" all the lets.

-- | A simple table holding a let-introduced identifier/name to its RHS.
--
-- Note that in case of a datatype-let (which has multiple identifiers&bindings), we add a table entry for each identifier of that datatype.
-- The multi-let-grouppings of the initial PIR program do not exist anymore in this representation.
type RhsTable tyname name uni a = M.Map
                              PLC.Unique
                              (Rhs tyname name uni a)

-- | An Rhs is a triple of Annotation, Recursivity, and its Binding.
--
-- If the RHS was prior belonging to a larger let-group, its Recursivity&Annotation is copied from the let-group's Recursivity&Annotation.
-- In other words the same Recursivity&Annotation is shared among the let-identifiers that were beloning to the same let-group.
type Rhs tyname name uni ann = (ann, Recursivity, Binding tyname name uni ann)

-- | This function takes a 'Term', cleans the 'Term' from all its 'Let'-bindings and stores those lets into a separate table.
-- Note that the output term is most-likely not a valid PIR program anymore, because it contains free unbound variables.
--
-- OPTIMIZE: this traversal may potentially be included/combined with the pass1.
removeLets :: forall name tyname uni a
            . (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
           => Term tyname name uni a
           -> (Term tyname name uni a, RhsTable tyname name uni a)
removeLets = flip runState M.empty . go
 where
   go :: Term tyname name uni a -> State (RhsTable tyname name uni a) (Term tyname name uni a)
   go = \case
         -- this overrides the 'termSubterms' functionality only for the 'Let' constructor
         Let a r bs tIn -> do
           forM_ bs $ \ b -> do
             b' <- bindingSubterms go b
             modify (M.insert (b'^.principal) (a, r, b'))
           go tIn
         t -> termSubterms go t



-- | Starts the 2nd pass from the 'Top' depth and the toplevel expression of the cleanedup term (devoid of any lets).
--
-- OPTIMIZE: We could potentially replace the pure descending ('Reader FloatData') of the 2nd pass, to 'State FloatData'. In such a case
-- this transformation might stop earlier, when the state becomes empty: i.e. no let-rhses are left to float.
p2Term :: forall name tyname uni a
       . (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique, Monoid a)
      => Term tyname name uni a --
      -> FloatData
      -> Term tyname name uni a
p2Term pir = goFloat Top pirClean -- start the 2nd pass by trying to float any lets around the top-level expression (body)
 where
  -- | Prior to starting the second pass, we clean the term from all its let-declarations and store them separately in a table.
  -- The 2nd pass will later re-introduce these let-declarations, potentially placing them differently than before, thus essentially "floating the lets".
  (pirClean :: Term tyname name uni a, rhsTable :: RhsTable tyname name uni a) = removeLets pir

  -- 2nd-pass functions
  ---------------------

  -- | visit each term to apply the float transformation
  goTerm :: Int -- ^ current depth
         -> FloatData -- ^ the lambdas we are searching for (to float some lets inside them)
         -> Term tyname name uni a
         -> Term tyname name uni a
  goTerm curDepth searchTable = \case
      -- we are only interested in lambdas/Lambdas
      LamAbs a n ty tBody -> LamAbs a n ty $ goAbs curDepth searchTable n tBody
      TyAbs a n k tBody  -> TyAbs a n k $ goAbs curDepth searchTable n tBody
      -- descend otherwise to apply the transformations to subterms
      t -> over termSubterms (goTerm curDepth searchTable) t

  -- | If a lambda/Lambda is found, the current location is updated (depth+lamname) and try to float its body
  goAbs :: PLC.HasUnique b b'
        => Int -- ^ current depth
        -> FloatData -- ^ the lambdas we are searching for (to float some lets inside them)
        -> b                  -- ^ lambda/Lambda's name
        -> Term tyname name uni a -- ^ lambda/Lambda's body
        -> Term tyname name uni a
  goAbs oldDepth floatData n tBody =
    let newLam = LamDep (oldDepth+1) (n^.PLC.unique.coerced)
    in goFloat newLam tBody floatData

  -- | We are currently INSIDE (exactly under) a lambda/Lambda body/Top (Top if we are right at the start of the algorithm)
  -- We try to see if we have some lets to float here based on our 1st-pass-table data (searchTable).
  goFloat :: Rank -- ^ the rank/location of the lambda above that has this body
         -> Term tyname name uni a                           -- ^ the body term
         -> FloatData -- ^ the lambdas we are searching for (to float some lets inside them)
         -> Term tyname name uni a                           -- ^ the transformed body term
  goFloat _ tBody [] = tBody
  goFloat aboveLamLoc tBody floatData@((searchingForDepth, searchingForLams_Lets) : restFloatData) =
    let curDepth = aboveLamLoc^.depth
    in case curDepth `compare` searchingForDepth of
      -- the minimum next depth we are looking for, is not this one, so just descend with the whole floatdata
      LT -> goTerm curDepth floatData tBody
      -- found depth, see if our lambda above is a lambda we are interested in (to float some lets)
      EQ ->
        -- transform the lam-body, passing the rest floatdata
        let tBody' = goTerm curDepth restFloatData tBody
        in case M.lookup aboveLamLoc searchingForLams_Lets of
             -- the lambda above-this-body has some let-rhses to insert (float) here.
             Just lets -> wrapLets lets curDepth restFloatData tBody'
             -- nothing to do for the lambda above, i.e. no let-rhses to insert here
             _         -> tBody'
      GT -> error "This shouldn't happen, because the algorithm takes care to stop descending when EQ is reached."


  -- | the dependency graph (as the one used by the deadcode elimination)
  -- but w/o the root node and only uses the name of the var (PLC.Unique) as the node id
  depGraph :: AM.AdjacencyMap PLC.Unique
  depGraph = AM.gmap (\case Variable u -> u; _ -> error "just for completion")
             $ AM.removeVertex Root -- we remove Root because we do not care about it
             $ runTermDeps pir

  -- | the dependency graph as before, but with datatype-related nodes merged/reduced under a single node per datatypebind a, see 'principal'.
  reducedDepGraph :: AM.AdjacencyMap PLC.Unique
  reducedDepGraph = M.foldr (\ (_,_,b) accGraph ->
                               let princ = b^.principal
                               -- note that: (replaceVertex princ princ == id)
                               in foldr (\ i -> AM.replaceVertex i princ) accGraph $ bindingIds b
                            ) depGraph rhsTable

  -- |take the strongly-connected components of the reduced dep graph, because it may contain loops (introduced by the LetRecs)
  -- topologically sort these sccs, since we rely on linear (sorted) scoping in our 'wrapLets' code generation
  topSortedSccs :: [AMN.AdjacencyMap PLC.Unique]
  topSortedSccs = fromMaybe (error "Cycle detected in the depgraph. This shouldn't happen in the first place.") $ AM.topSort $ AM.scc reducedDepGraph

  -- | Groups a given set of lets into one or more multilets and wraps these multilets around a given term.
  -- The grouping is done through the strongly-connected components
  -- The input lets is not sorted w.r.t. linear scoping, so this function uses the topological-sort of these SCCs,
  -- to figure out the correct (dependend/linear) order in which to generate these new multilets.
  --
  -- Note that the resulting term is wrapped with linear-scope-sorted LetRecs and LetNonRecs (interspersed between each other because letnonrec and letrec syntax cannot be combined)
  -- Example: `let {i = e, ...} in let rec {j = e, ...} in let rec {...} in let {...} in ..... in originalTerm`
  wrapLets :: S.Set PLC.Unique -- ^ all the let identifiers to wrap around this term
           -> Int -- ^ current depth
           -> FloatData -- ^ the remaining data to be floated
           -> Term tyname name uni a                           -- ^ the term to be wrapped
           -> Term tyname name uni a                           -- ^ the final wrapped term
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


-- | The main transformation function (Term -> Term) that returns a term with all lets floated as outwards as possible (full laziness).
-- Traverses the AST:
-- 1stpass: to collect the maximum ranks (positions) of all lets
-- 2ndpass:  to remove all its lets and place them back (float them) in their maximum ranks (positions).
--
-- Note: this transformation requires that the PLC.rename compiler-pass has prior been run.
floatTerm :: forall name tyname uni a
           . (Ord (tyname a), PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique, Monoid a)
          => Term tyname name uni a -> Term tyname name uni a
floatTerm pir = p2Term pir
                -- give the floatdata of the 1st pass to the start of the 2nd pass
              $ p1Term pir


-- Helpers
----------

-- | Returns a single 'Unique' for a particular binding.
-- We need this because let-datatypes introduce multiple identifiers, but in our 'RhsTable', we use a single Unique as the key. See also: 'bindingIds'
principal :: (PLC.HasUnique (tyname a) PLC.TypeUnique, PLC.HasUnique (name a) PLC.TermUnique)
            => Getting r (Binding tyname name uni a) PLC.Unique
principal = to $ \case TermBind _ _ (VarDecl _ n _) _ -> n ^. PLC.unique . coerced
                       TypeBind _ (TyVarDecl _ n _) _ -> n ^. PLC.unique . coerced
                       -- arbitrary: uses the match-function's unique as the principal unique of this data binding group
                       DatatypeBind _ (Datatype _ _ _ matchFunc _) -> matchFunc ^. PLC.unique . coerced
