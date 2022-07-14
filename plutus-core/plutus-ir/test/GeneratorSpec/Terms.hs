-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module GeneratorSpec.Terms where

import PlutusCore.Generators.PIR

import Control.Monad.Reader

import Data.Char
import Data.Either
import Data.List hiding (insert)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map qualified as Map
import Text.Printf

import PlutusCore.Name
import PlutusIR
import PlutusIR.Core.Instance.Pretty.Readable

import Test.QuickCheck

-- * Core properties for PIR generators

-- | Test that our generators only result in well-typed terms.
-- Note, the counterexamples from this property are not shrunk (see why below).
-- See Note [Debugging generators that don't generate well-typed/kinded terms/types]
-- and the utility properties below when this property fails.
prop_genTypeCorrect :: Bool -> Property
prop_genTypeCorrect debug =
  -- Note, we don't shrink this term here because a precondition of shrinking is that
  -- the term we are shrinking is well-typed. If it is not, the counterexample we get
  -- from shrinking will be nonsene.
  forAllDoc "ty,tm" (if debug then genTypeAndTermDebug_ else genTypeAndTerm_) (const []) $ \ (ty, tm) -> typeCheckTerm tm ty

-- | Test that when we generate a fully applied term we end up
-- with a well-typed term.
prop_genWellTypedFullyApplied :: Property
prop_genWellTypedFullyApplied =
  forAllDoc "ty, tm" genTypeAndTerm_ shrinkClosedTypedTerm $ \ (ty, tm) ->
  -- No shrinking here because if `genFullyApplied` is wrong then the shrinking
  -- will be wrong too. See `prop_genTypeCorrect`.
  forAllDoc "ty', tm'" (genFullyApplied ty tm) (const []) $ \ (ty', tm') ->
  typeCheckTerm tm' ty'

-- | Test that shrinking a well-typed term results in a well-typed term
prop_shrinkTermSound :: Property
prop_shrinkTermSound =
  forAllDoc "ty,tm"   genTypeAndTerm_ shrinkClosedTypedTerm $ \ (ty, tm) ->
  let shrinks = shrinkClosedTypedTerm (ty, tm) in
  -- While we generate well-typed terms we still need this check here for
  -- shrinking counterexamples to *this* property. If we find a term whose
  -- shrinks aren't well-typed we want to find smaller *well-typed* terms
  -- whose shrinks aren't well typed.
  -- Importantly, this property is only interesting when
  -- shrinking itself is broken, so we can only use the
  -- parts of shrinking that happen to be OK.
  isRight (typeCheckTerm tm ty) ==>
  -- We don't want to let the shrinker get away with being empty, so we ignore empty shrinks. QuickCheck will give
  -- up and print an error if the shrinker returns the empty list too often.
  not (null shrinks) ==>
  assertNoCounterexamples $ lefts
    [ ((ty, tm), scopeCheckTyVars Map.empty (ty, tm), ) <$> typeCheckTerm tm ty
    | (ty, tm) <- shrinks
    ]

-- * Utility tests for debugging generators that behave weirdly

-- | Test that `findInstantiation` results in a well-typed instantiation.
prop_findInstantiation :: Property
prop_findInstantiation =
  forAllDoc "ctx"    genCtx                      (const [])       $ \ ctx ->
  forAllDoc "ty"     (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ ty ->
  forAllDoc "target" (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ target ->
  assertNoCounterexamples $ lefts
    [ (n ,) <$> errOrFine
    | n <- [0..arity ty+3]
    , let errOrFine = do
            insts <- findInstantiation ctx n target ty
            checkInst ctx x ty insts target
    ]
  where
    x = Name "x" (toEnum 0)
    arity (TyForall _ _ _ a) = arity a
    arity (TyFun _ _ b)      = 1 + arity b
    arity _                  = 0

    -- Check that building a "minimal" term that performs the instantiations in
    -- `insts` produces a well-typed term.
    checkInst ctx x ty insts target = typeCheckTermInContext ctx tmCtx tm target
      where
        -- Build a term and a context from `insts` that consists of
        -- `tm @ty` for every `InstApp ty` in `insts` and `tm y` for
        -- a fresh variable `y : ty` for every `InstArg ty` in `insts`.
        (tmCtx, tm) = go (toEnum 1) (Map.singleton x ty) (Var () x) insts
        go _ tmCtx tm [] = (tmCtx, tm)
        go i tmCtx tm (InstApp ty : insts) = go i tmCtx (TyInst () tm ty) insts
        go i tmCtx tm (InstArg ty : insts) = go (succ i) (Map.insert y ty tmCtx)
                                                         (Apply () tm (Var () y)) insts
          where y = Name "y" i

-- | Check what's in the leaves of the generated data
prop_stats_leaves :: Property
prop_stats_leaves =
  -- No shrinking here because we are only collecting stats
  forAllDoc "_,tm" genTypeAndTerm_ (const []) $ \ (_, tm) ->
  tabulate "leaves" (map (filter isAlpha . show . prettyPirReadable) $ leaves tm) $ property True
  where
    -- Figure out what's at the leaves of the AST,
    -- including variable names, error, and builtins.
    leaves (Var _ x)        = [x]
    leaves (TyInst _ a _)   = leaves a
    leaves (Let _ _ _ b)    = leaves b
    leaves (LamAbs _ _ _ b) = leaves b
    leaves (Apply _ a b)    = leaves a ++ leaves b
    leaves Error{}          = [Name "error" $ toEnum 0]
    leaves Builtin{}        = [Name "builtin" $ toEnum 0]
    leaves _                = []

-- | Check the ratio of duplicate shrinks
prop_stats_numShrink :: Property
prop_stats_numShrink =
  -- No shrinking here because we are only collecting stats
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (ty, tm) ->
  let shrinks = shrinkClosedTypedTerm (ty, tm)
      n = fromIntegral (length shrinks)
      u = fromIntegral (length $ nub shrinks)
      r | n > 0     = (n - u) / n :: Double
        | otherwise = 0
  in tabulate "r" [printf "%0.1f" r] True

-- | Specific test that `inhabitType` returns well-typed things
prop_inhabited :: Property
prop_inhabited =
  -- No shrinking here because if the generator
  -- generates nonsense shrinking will be nonsense.
  forAllDoc "ty,tm" (genInhab mempty) (const []) $ \ (ty, tm) -> typeCheckTerm tm ty
  where
    -- Generate some datatypes and then immediately call
    -- `inhabitType` to test `inhabitType` directly instead
    -- of through the whole term generator. Quick-ish way
    -- of debugging "clever hacks" in `inhabitType`.
    genInhab ctx = runGenTm $ local (\ e -> e { geTypes = ctx }) $
      genDatatypeLets $ \ dats -> do
        ty <- genType Star
        tm <- inhabitType ty
        return (ty, foldr (\ dat -> Let () NonRec (DatatypeBind () dat :| [])) tm dats)

-- | Check that there are no one-step shrink loops
prop_noTermShrinkLoops :: Property
prop_noTermShrinkLoops =
  -- Note that we need to remove x from the shrinks of x here because
  -- a counterexample to this property is otherwise guaranteed to
  -- go into a shrink loop.
  forAllDoc "ty,tm" genTypeAndTerm_ (\x -> filter (/= x) $ shrinkClosedTypedTerm x) $ \ tytm ->
  tytm `notElem` shrinkClosedTypedTerm tytm
