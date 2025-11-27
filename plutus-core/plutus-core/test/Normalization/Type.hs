{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Normalization.Type
  ( test_typeNormalization
  ) where

import PlutusCore
import PlutusCore.Generators.Hedgehog.AST
import PlutusCore.MkPlc
import PlutusCore.Normalize
import PlutusCore.Test

import Control.Monad.Morph (hoist)

import Hedgehog
import Hedgehog.Internal.Property (forAllT)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

test_appAppLamLam :: IO ()
test_appAppLamLam = do
  let integer2 = mkTyBuiltin @_ @Integer @DefaultUni ()
      Normalized integer2' = runQuote $ do
        x <- freshTyName "x"
        y <- freshTyName "y"
        normalizeType $
          mkIterTyAppNoAnn
            (TyLam () x (Type ()) (TyLam () y (Type ()) $ TyVar () y))
            [integer2, integer2]
  integer2 @?= integer2'

test_normalizeTypesInIdempotent :: Property
test_normalizeTypesInIdempotent =
  mapTestLimitAtLeast 300 (`div` 10) . property . hoist (pure . runQuote) $ do
    termNormTypes <- forAllT $ runAstGen (genTerm @DefaultFun) >>= normalizeTypesIn
    termNormTypes' <- normalizeTypesIn termNormTypes
    termNormTypes === termNormTypes'

test_typeNormalization :: TestTree
test_typeNormalization =
  testGroup
    "typeNormalization"
    [ testCase "appAppLamLam" test_appAppLamLam
    , testPropertyNamed
        "normalizeTypesInIdempotent"
        "normalizeTypesInIdempotent"
        test_normalizeTypesInIdempotent
    ]
