{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}

module UntypedPlutusCore.Transform.Cse (cse) where

import PlutusCore (MonadQuote, Name, Rename, freshName, rename)
import PlutusCore.Builtin (ToBuiltinMeaning (BuiltinSemanticsVariant))
import UntypedPlutusCore.Core
import UntypedPlutusCore.Purity (isWorkFree)
import UntypedPlutusCore.AstSize (termAstSize)
import UntypedPlutusCore.Transform.Simplifier (SimplifierStage (CSE), SimplifierT,
                                               recordSimplification)

import Control.Arrow ((>>>))
import Control.Lens (foldrOf, transformOf)
import Control.Monad (join, void)
import Control.Monad.Trans.Class (MonadTrans (lift))
import Control.Monad.Trans.Reader (ReaderT (runReaderT), ask, local)
import Control.Monad.Trans.State.Strict (State, evalState, get, put)
import Data.Foldable as Foldable (foldl')
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as Map
import Data.List.Extra (isSuffixOf, sortOn)
import Data.Ord (Down (..))
import Data.Proxy (Proxy (..))
import Data.Traversable (for)
import Data.Tuple.Extra (snd3, thd3)
import PlutusCore.Arity (builtinArity)

{- Note [CSE]

-------------------------------------------------------------------------------
1. Simplifications
-------------------------------------------------------------------------------

This is a simplified (i.e., not fully optimal) implementation of CSE. The one simplification
we made is:

- No alpha equivalence check, i.e., `\x -> x` and `\y -> y` are considered different expressions.

-------------------------------------------------------------------------------
2. How does it work?
-------------------------------------------------------------------------------

We use the following example to explain how the implementation works:

\x y -> (1+(2+x))
        +
        (case y [ (1+(2+x)) + (3+x)
                , (2+x) + (3+x)
                , 4+x
                ]
        )

The implementation makes several passes on the given term. The first pass collects builtin
arity information as described above.

In the second pass, we assign a unique ID to each `LamAbs`, `Delay`, and each `Case` branch.
Then, we annotate each subterm with a path, consisting of IDs encountered from the root
to that subterm (not including itself). The reason to do this is because `LamAbs`, `Delay`,
and `Case` branches represent places where computation stops, i.e., subexpressions are not
immediately evaluated, and may not be evaluated at all.

In the above example, the ID of `\x` is 0, the ID of `\y` is 1, and the IDs of the
three case branches are 2, 3, 4 (the actual numbers don't matter, as long as they are unique).
The path for the first `1+(2+x)` and the first `2+x` is "0.1"; the path for the second
`1+(2+x)` and the second `2+x` is "0.1.2"; the path for `4+x` is "0.1.4".

In the third pass, we calculate a count for each `(term, path)` pair, where `term` is a
non-workfree term, and `path` is its path. If the same term has two paths, and one is an
ancestor (i.e., prefix) of the other, we increment the count for the ancestor path in both
instances.

In the above example, there are three occurrences of `2+x`, whose paths are "0.1", "0.1.2"
and "0.1.3", respectively. The first path is an ancestor of the latter two. Therefore,
the count for `(2+x, "0.1")` is 3, while the count for `(2+x, "0.1.2")` and `(2+x, "0.1.3")`
is 0. The following all have a count of 1: `(3+x, "0.1.2")`, `(3+x, "0.1.3")` and
`(4+x, "0.1.4")`.

Now, each `(term, path)` pair whose count is greater than 1 is a CSE candidate.
In the above example, the CSE candidates are `(2+x, "0.1")` and `(1+(2+x), "0.1")`.
Note that `3+x` is not a CSE candidate, because it has two paths, and neither has a count
greater than 1. `2+` is also not a CSE candidate, because it is workfree.

The CSE candidates are then processed in descending order of their `termAstSize`s. For each CSE
candidate, we generate a fresh variable, create a LamAbs for it under its path, and substitute
it for all occurrences in the original term whose paths are descendents (or self) of
the candidate's path. The order is because a bigger expression may contain a small subexpression.

In the above example, we first process CSE candidate `(1+(2+x), "0.1")`. We create a fresh
variable `cse1` for it, perform substitution, and create a `LamAbs` under path "0.1" (i.e., around
the body of `y`). After processing this CSE candidate, the original term becomes

\x y -> (\cse1 -> cse1
                  +
                  (case y [ cse1 + (3+x)
                          , (2+x) + (3+x)
                          , 4+x
                          ]
        ) (1+(2+x))

The second CSE candidate is processed similarly, and the final result is

\x y -> (\cse2 -> (\cse1 -> cse1
                            +
                            (case y [ cse1 + (3+x)
                                    , cse2 + (3+x)
                                    , 4+x
                                    ]
                  ) (1+cse2)
        ) (2+x)

Here's another example:

force (force ifThenElse
         (lessThanEqualsInteger 0 0)
         (delay ((1+2) + (1+2)))
         (delay (1+2))
      )

In this case, the first two occurrences of `1+2` can be CSE'd, but the third occurrence
can not. This is ensured by checking the path when substituting `cse1` for `1+2`. The result is

force (force ifThenElse
         (lessThanEqualsInteger 0 0)
         (delay ((\cse1 -> cse1 + cse1) (1+2))
         (delay (1+2))
      )

-------------------------------------------------------------------------------
3. When should CSE run?
-------------------------------------------------------------------------------

CSE should run for multiple iterations, and should interleave with inlining. The following
example illustrates why:

\x ->
  f
    ((\y -> 1+(y+y)) (0+x))
    ((\z -> 2+(z+z)) (0+x))

There is no inlining opportunity in this term. After the first iteration of CSE, where
the common subepxression is `0+x`, we get:

\x ->
  (\cse1 ->
    f
      ((\y -> 1+(y+y)) cse1)
      ((\z -> 2+(z+z)) cse1)
  ) (0+x)

Now `y` and `z` can be inlined, after which we get

\x ->
  (\cse1 ->
    f
      (1+(cse1+cse1))
      (2+(cse1+cse1))
  ) (0+x)

Now there's a new common subexpression: `cse1+cse1`. So another iteration of CSE is
needed, yielding:

\x ->
  (\cse1 ->
    (\cse2 ->
      f
        (1+cse2)
        (2+cse2)
    ) (cse1+cse1)
  ) (0+x)

With this example in mind, one may be tempted to make CSE part of the simplifier, and simply
run it along with the rest of the simplifier. That is, however, a bad idea. CSE does the reverse
of inlining; inlining tends to expose more optimization opportunities, and conversely, CSE
tends to destroy optimization opportunities. Running CSE on a not-fully-optimized program
may cause many optimization opportunities to be permanently lost. Give it a try if you want
to see how bad it is!

Therefore, this is what we do: first run the simplifier iterations. Then, run the CSE iterations,
interleaving with the simplifier. For example, suppose max-simplifier-iterations-uplc=12, and
max-cse-iterations=4. We first run 12 iterations of the simplifier, then run 4 iterations
of CSE, with a simplifier pass after each iteration of CSE (i.e., the simplifier is run for a
total of 16 times).

Finally, since CSE can change the order or the number of occurrences of effects, it is only run
when conservative optimization is off.
-}

-- | In reverse order, e.g., "1.2.3" is `[3, 2, 1]`.
type Path = [Int]

isAncestorOrSelf :: Path -> Path -> Bool
isAncestorOrSelf = isSuffixOf

data CseCandidate uni fun ann = CseCandidate
  { ccFreshName     :: Name
  , ccTerm          :: Term Name uni fun ()
  , ccAnnotatedTerm :: Term Name uni fun (Path, ann)
  -- ^ `ccTerm` is needed for equality comparison, while `ccAnnotatedTerm` is needed
  -- for the actual substitution. They are always the same term barring the annotations.
  }

cse ::
  ( MonadQuote m
  , Hashable (Term Name uni fun ())
  , Rename (Term Name uni fun ann)
  , ToBuiltinMeaning uni fun
  ) =>
  BuiltinSemanticsVariant fun ->
  Term Name uni fun ann ->
  SimplifierT Name uni fun ann m (Term Name uni fun ann)
cse builtinSemanticsVariant t0 = do
  t <- rename t0
  let annotated = annotate t
      commonSubexprs =
        -- Processed the common subexpressions in descending order of `termAstSize`.
        -- See Note [CSE].
        sortOn (Down . termAstSize)
          . fmap snd3
          -- A subexpression is common if the count is greater than 1.
          . filter ((> 1) . thd3)
          . join
          . Map.elems
          $ countOccs builtinSemanticsVariant annotated
  result <- mkCseTerm commonSubexprs annotated
  recordSimplification t0 CSE result
  return result

-- | The second pass. See Note [CSE].
annotate :: Term name uni fun ann -> Term name uni fun (Path, ann)
annotate = flip evalState 0 . flip runReaderT [] . go
  where
    -- The integer state is the highest ID assigned so far.
    -- The reader context is the current path.
    go :: Term name uni fun ann -> ReaderT Path (State Int) (Term name uni fun (Path, ann))
    go t = do
      path <- ask
      case t of
        Apply ann fun arg -> Apply (path, ann) <$> go fun <*> go arg
        Force ann body -> Force (path, ann) <$> go body
        Constr ann i args -> Constr (path, ann) i <$> traverse go args
        Constant ann val -> pure $ Constant (path, ann) val
        Error ann -> pure $ Error (path, ann)
        Builtin ann fun -> pure $ Builtin (path, ann) fun
        Var ann name -> pure $ Var (path, ann) name
        LamAbs ann n body -> do
          freshId <- (+ 1) <$> lift get
          lift $ put freshId
          LamAbs (path, ann) n <$> local (freshId :) (go body)
        Delay ann body -> do
          freshId <- (+ 1) <$> lift get
          lift $ put freshId
          Delay (path, ann) <$> local (freshId :) (go body)
        Case ann scrut branches ->
          Case (path, ann)
            <$> go scrut
            <*> ( for branches $ \br -> do
                    freshId <- (+ 1) <$> lift get
                    lift $ put freshId
                    local (freshId :) (go br)
                )

-- | The third pass. See Note [CSE].
countOccs ::
  forall name uni fun ann.
  (Hashable (Term name uni fun ()), ToBuiltinMeaning uni fun) =>
  BuiltinSemanticsVariant fun ->
  Term name uni fun (Path, ann) ->
  -- | Here, the value of the inner map not only contains the count, but also contains
  -- the annotated term, corresponding to the term that is the key of the outer map.
  -- The annotated terms need to be recorded since they will be used for substitution.
  HashMap (Term name uni fun ()) [(Path, Term name uni fun (Path, ann), Int)]
countOccs builtinSemanticsVariant = foldrOf termSubtermsDeep addToMap Map.empty
  where
    addToMap ::
      Term name uni fun (Path, ann) ->
      HashMap (Term name uni fun ()) [(Path, Term name uni fun (Path, ann), Int)] ->
      HashMap (Term name uni fun ()) [(Path, Term name uni fun (Path, ann), Int)]
    addToMap t0
      -- We don't consider work-free terms for CSE, because doing so may or may not
      -- have a size benefit, but certainly doesn't have any cost benefit (the cost
      -- will in fact be slightly higher due to the additional application).
      | isWorkFree builtinSemanticsVariant t0
        || not (isBuiltinSaturated t0)
        || isForcingBuiltin t0 =
          id
      | otherwise =
          Map.alter
            ( \case
                Nothing -> Just [(path, t0, 1)]
                Just paths -> Just $ combinePaths t0 path paths
            )
            t
      where
        t = void t0
        path = fst (termAnn t0)

    isBuiltinSaturated =
      splitApplication >>> \case
        (Builtin _ fun, args) ->
          length args >= length (builtinArity (Proxy @uni) builtinSemanticsVariant fun)
        _term -> True

    isForcingBuiltin = \case
      Builtin{} -> True
      Force _ t -> isForcingBuiltin t
      _ -> False

-- | Combine a new path with a number of existing (path, count) pairs.
combinePaths ::
  forall name uni fun ann.
  Term name uni fun (Path, ann) ->
  Path ->
  [(Path, Term name uni fun (Path, ann), Int)] ->
  [(Path, Term name uni fun (Path, ann), Int)]
combinePaths t path = go 1
  where
    go ::
      Int ->
      [(Path, Term name uni fun (Path, ann), Int)] ->
      [(Path, Term name uni fun (Path, ann), Int)]
    -- The new path is not a descendent-or-self of any existing path.
    go acc [] = [(path, t, acc)]
    go acc ((path', t', cnt) : paths)
      -- The new path is an ancestor-or-self of an existing path.
      -- Take over all counts of the existing path, remove the existing path,
      -- and continue.
      | path `isAncestorOrSelf` path' = go (acc + cnt) paths
      -- The new path is a descendent-or-self of an existing path.
      -- Increment the count for the existing path. There can only be one such
      -- existing path, so we don't need to recurse here.
      | path' `isAncestorOrSelf` path = (path', t', cnt + 1) : paths
      | otherwise = (path', t', cnt) : go acc paths

mkCseTerm ::
  forall uni fun ann m.
  (MonadQuote m, Eq (Term Name uni fun ())) =>
  [Term Name uni fun (Path, ann)] ->
  -- | The original annotated term
  Term Name uni fun (Path, ann) ->
  m (Term Name uni fun ann)
mkCseTerm ts t = do
  cs <- traverse mkCseCandidate ts
  pure . fmap snd $ Foldable.foldl' (flip applyCse) t cs

applyCse ::
  forall uni fun ann.
  (Eq (Term Name uni fun ())) =>
  CseCandidate uni fun ann ->
  Term Name uni fun (Path, ann) ->
  Term Name uni fun (Path, ann)
applyCse c = mkLamApp . transformOf termSubterms substCseVarForTerm
  where
    candidatePath = fst (termAnn (ccAnnotatedTerm c))

    substCseVarForTerm :: Term Name uni fun (Path, ann) -> Term Name uni fun (Path, ann)
    substCseVarForTerm t =
      if currTerm == ccTerm c && candidatePath `isAncestorOrSelf` currPath
        then Var (termAnn t) (ccFreshName c)
        else t
      where
        currTerm = void t
        currPath = fst (termAnn t)

    mkLamApp :: Term Name uni fun (Path, ann) -> Term Name uni fun (Path, ann)
    mkLamApp t
      | currPath == candidatePath =
          Apply
            (termAnn t)
            (LamAbs (termAnn t) (ccFreshName c) t)
            (ccAnnotatedTerm c)
      | currPath `isAncestorOrSelf` candidatePath = case t of
          Var ann name            -> Var ann name
          LamAbs ann name body    -> LamAbs ann name (mkLamApp body)
          Apply ann fun arg       -> Apply ann (mkLamApp fun) (mkLamApp arg)
          Force ann body          -> Force ann (mkLamApp body)
          Delay ann body          -> Delay ann (mkLamApp body)
          Constant ann val        -> Constant ann val
          Builtin ann fun         -> Builtin ann fun
          Error ann               -> Error ann
          Constr ann i ts         -> Constr ann i (mkLamApp <$> ts)
          Case ann scrut branches -> Case ann (mkLamApp scrut) (mkLamApp <$> branches)
      | otherwise = t
      where
        currPath = fst (termAnn t)

-- | Generate a fresh variable for the common subexpression.
mkCseCandidate ::
  forall uni fun ann m.
  (MonadQuote m) =>
  Term Name uni fun (Path, ann) ->
  m (CseCandidate uni fun ann)
mkCseCandidate t = CseCandidate <$> freshName "cse" <*> pure (void t) <*> pure t
