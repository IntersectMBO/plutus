-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusIR.Generators.QuickCheck.Tests where

import PlutusPrelude

import PlutusCore.Generators.QuickCheck
import PlutusIR.Generators.QuickCheck

import PlutusCore.Builtin (fromValue)
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Name.Unique
import PlutusCore.Pretty
import PlutusCore.Quote
import PlutusCore.Rename
import PlutusCore.Test (toUPlc)
import PlutusCore.Version (latestVersion)
import PlutusIR
import PlutusIR.Test ()
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek
  ( restrictingLarge
  , runCekNoEmit
  , unsafeSplitStructuralOperational
  )

import Control.Exception
import Control.Monad.Except
import Control.Monad.Reader
import Data.Char
import Data.Either
import Data.HashMap.Strict qualified as HashMap
import Data.Hashable
import Data.Map.Strict qualified as Map
import Test.QuickCheck

-- | 'rename' a 'Term' and 'show' it afterwards.
showRenameTerm :: Term TyName Name DefaultUni DefaultFun () -> String
showRenameTerm = show . runQuote . rename

-- | Same as 'nub', but relies on 'Hashable' and is therefore asymptotically faster.
nubHashableOn :: Hashable b => (a -> b) -> [a] -> [a]
nubHashableOn f = HashMap.elems . HashMap.fromList . map (\x -> (f x, x))

-- We need this for checking the behavior of the shrinker (in particular, whether a term shrinks
-- to itself, which would be a bug, or how often a term shrinks to the same thing multiple times
-- within a single step). Should we move this to @plutus-ir@ itself? Not sure, but it's safe to
-- place it here, since nothing can depend on a test suite (apart from modules from within this test
-- suite), hence no conflicting orphans can occur.
instance Eq (Term TyName Name DefaultUni DefaultFun ()) where
  -- Quick-and-dirty implementation in terms of 'Show'.
  -- We generally consider equality modulo alpha, hence the call to 'rename'.
  (==) = (==) `on` showRenameTerm

-- * Core properties for PIR generators

prop_genTypeCorrect :: Property
prop_genTypeCorrect = p_genTypeCorrect False

{-| Test that our generators only result in well-typed terms.
Note, the counterexamples from this property are not shrunk (see why below).
See Note [Debugging generators that don't generate well-typed/kinded terms/types]
and the utility properties below when this property fails. -}
p_genTypeCorrect :: Bool -> Property
p_genTypeCorrect debug = withMaxSuccess 200 $ do
  -- Note, we don't shrink this term here because a precondition of shrinking is that
  -- the term we are shrinking is well-typed. If it is not, the counterexample we get
  -- from shrinking will be nonsene.
  let gen = if debug then genTypeAndTermDebug_ else genTypeAndTerm_
  forAllDoc "ty,tm" gen (const []) $ \(ty, tm) -> typeCheckTerm tm ty

{-| Test that when we generate a fully applied term we end up
with a well-typed term. -}
prop_genWellTypedFullyApplied :: Property
prop_genWellTypedFullyApplied = withMaxSuccess 50 $
  forAllDoc "ty, tm" genTypeAndTerm_ shrinkClosedTypedTerm $ \(ty, tm) ->
    -- No shrinking here because if `genFullyApplied` is wrong then the shrinking
    -- will be wrong too. See `prop_genTypeCorrect`.
    forAllDoc "ty', tm'" (genFullyApplied ty tm) (const []) $ \(ty', tm') ->
      typeCheckTerm tm' ty'

-- | Test that shrinking a well-typed term results in a well-typed term
prop_shrinkTermSound :: Property
-- The test is disabled, because it's exponential and was hanging CI.
prop_shrinkTermSound = withMaxSuccess 0 $
  forAllDoc "ty,tm" genTypeAndTerm_ shrinkClosedTypedTerm $ \(ty, tm) ->
    let shrinks = shrinkClosedTypedTerm (ty, tm)
     in -- While we generate well-typed terms we still need this check here for
        -- shrinking counterexamples to *this* property. If we find a term whose
        -- shrinks aren't well-typed we want to find smaller *well-typed* terms
        -- whose shrinks aren't well typed.
        -- Importantly, this property is only interesting when
        -- shrinking itself is broken, so we can only use the
        -- parts of shrinking that happen to be OK.
        isRight (typeCheckTerm tm ty) ==>
          -- We don't want to let the shrinker get away with being empty, so we ignore empty
          -- shrinks. QuickCheck will give up and print an error if the shrinker returns the empty list too
          -- often.
          not (null shrinks) ==>
            assertNoCounterexamples $
              lefts
                [ first ((ty', tm'),) $ typeCheckTerm tm' ty'
                | (ty', tm') <- shrinks
                ]

-- * Utility tests for debugging generators that behave weirdly

-- | Test that `findInstantiation` results in a well-typed instantiation.
prop_findInstantiation :: Property
prop_findInstantiation = withMaxSuccess 1000 $
  forAllDoc "ctx" genCtx (const []) $ \ctx0 ->
    forAllDoc "ty" (genTypeWithCtx ctx0 $ Type ()) (shrinkType ctx0) $ \ty0 ->
      forAllDoc "target" (genTypeWithCtx ctx0 $ Type ()) (shrinkType ctx0) $ \target ->
        assertNoCounterexamples $
          lefts
            [ first (n,) $ checkInst ctx0 x0 ty0 insts target
            | n <- [0 .. arity ty0 + 3]
            , Right insts <- [findInstantiation ctx0 n target ty0]
            ]
  where
    x0 = Name "x" (toEnum 0)
    arity (TyForall _ _ _ a) = arity a
    arity (TyFun _ _ b) = 1 + arity b
    arity _ = 0

    -- Check that building a "minimal" term that performs the instantiations in
    -- `insts` produces a well-typed term.
    checkInst ctx1 x1 ty1 insts1 target = typeCheckTermInContext ctx1 tmCtx1 tm1 target
      where
        -- Build a term and a context from `insts` that consists of
        -- `tm @ty` for every `InstApp ty` in `insts` and `tm y` for
        -- a fresh variable `y : ty` for every `InstArg ty` in `insts`.
        (tmCtx1, tm1) = go (toEnum 1) (Map.singleton x1 ty1) (Var () x1) insts1
        go _ tmCtx tm [] = (tmCtx, tm)
        go i tmCtx tm (InstApp ty : insts) = go i tmCtx (TyInst () tm ty) insts
        go i tmCtx tm (InstArg ty : insts) =
          go
            (succ i)
            (Map.insert y ty tmCtx)
            (Apply () tm (Var () y))
            insts
          where
            y = Name "y" i

-- | Check what's in the leaves of the generated data
prop_stats_leaves :: Property
prop_stats_leaves = withMaxSuccess 10 $
  -- No shrinking here because we are only collecting stats
  forAllDoc "_,tm" genTypeAndTerm_ (const []) $ \(_, tm) ->
    tabulate "leaves" (map (filter isAlpha . show . prettyReadable) $ leaves tm) $ property True
  where
    -- Figure out what's at the leaves of the AST,
    -- including variable names, error, and builtins.
    leaves (Var _ x) = [x]
    leaves (TyInst _ a _) = leaves a
    leaves (Let _ _ _ b) = leaves b
    leaves (LamAbs _ _ _ b) = leaves b
    leaves (Apply _ a b) = leaves a ++ leaves b
    leaves Error {} = [Name "error" $ toEnum 0]
    leaves Builtin {} = [Name "builtin" $ toEnum 0]
    leaves _ = []

-- | Check the ratio of duplicate shrinks
prop_stats_numShrink :: Property
-- The test is disabled, because it's exponential and was hanging CI.
prop_stats_numShrink = withMaxSuccess 0 $
  -- No shrinking here because we are only collecting stats
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \(ty, tm) ->
    let shrinks = map snd $ shrinkClosedTypedTerm (ty, tm)
        n = length shrinks
        u = length $ nubHashableOn showRenameTerm shrinks
        r
          | n > 0 = 5 * ((n - u) * 20 `div` n)
          | otherwise = 0
     in tabulate "distribution | duplicates" ["         | " ++ show r ++ "%"] True

-- | Specific test that `inhabitType` returns well-typed things
prop_inhabited :: Property
prop_inhabited = withMaxSuccess 50 $
  -- No shrinking here because if the generator
  -- generates nonsense shrinking will be nonsense.
  forAllDoc "ty,tm" (genInhab mempty) (const []) $
    \(ty, tm) -> typeCheckTerm tm ty
  where
    -- Generate some datatypes and then immediately call
    -- `inhabitType` to test `inhabitType` directly instead
    -- of through the whole term generator. Quick-ish way
    -- of debugging "clever hacks" in `inhabitType`.
    genInhab ctx = runGenTm $
      local (\e -> e {geTypes = ctx}) $
        genDatatypeLets $ \dats -> do
          ty <- genType $ Type ()
          tm <- inhabitType ty
          return (ty, foldr (\dat -> Let () NonRec (DatatypeBind () dat :| [])) tm dats)

-- | Check that there are no one-step shrink loops
prop_noTermShrinkLoops :: Property
-- The test is disabled, because it's exponential and was hanging CI.
prop_noTermShrinkLoops = withMaxSuccess 0
  $
  -- Note that we need to remove x from the shrinks of x here because
  -- a counterexample to this property is otherwise guaranteed to
  -- go into a shrink loop.
  forAllDoc
    "ty,tm"
    genTypeAndTerm_
    (\(ty', tm') -> filter ((/= tm') . snd) $ shrinkClosedTypedTerm (ty', tm'))
  $ \(ty, tm) ->
    tm `notElem` map snd (shrinkClosedTypedTerm (ty, tm))

-- | Check that evaluation of the given term doesn't fail with a structural error.
noStructuralErrors :: UPLC.Term Name DefaultUni DefaultFun () -> IO ()
noStructuralErrors term =
  -- Throw on a structural evaluation error and succeed on both an operational evaluation error and
  -- evaluation success.
  void . evaluate . unsafeSplitStructuralOperational . fst $ do
    -- Using 'restrictingLarge' so that evaluation of the arbitrarily generated term always finishes
    -- in reasonable time even if evaluation loops (in which case we'll get an out-of-budget
    -- failure).
    runCekNoEmit defaultCekParametersForTesting restrictingLarge term

-- | Test that evaluation of well-typed terms doesn't fail with a structural error.
prop_noStructuralErrors :: Property
prop_noStructuralErrors = withMaxSuccess 99 $
  forAllDoc "ty,tm" genTypeAndTerm_ shrinkClosedTypedTerm $ \(_, termPir) -> ioProperty $ do
    termUPlc <-
      fmap UPLC._progTerm . modifyError (userError . displayException) . toUPlc $
        Program () latestVersion termPir
    noStructuralErrors termUPlc

-- | Test that evaluation of an ill-typed terms fails with a structural error.
prop_yesStructuralErrors :: Property
prop_yesStructuralErrors =
  expectFailure . ioProperty $
    noStructuralErrors $
      UPLC.Apply () (fromValue True) (fromValue ())
