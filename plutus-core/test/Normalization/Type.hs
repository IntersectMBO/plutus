{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Normalization.Type
    ( test_typeNormalization
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Generators.AST
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Normalize

import           Control.Monad.Morph                (hoist)

import           Hedgehog
import           Hedgehog.Internal.Property         (forAllT)
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog

test_appAppLamLam :: IO ()
test_appAppLamLam = do
    let integer2 = mkTyBuiltin @Integer @DefaultUni ()
        Normalized integer2' = runQuote $ do
            x <- freshTyName "x"
            y <- freshTyName "y"
            normalizeType $ mkIterTyApp ()
                (TyLam () x (Type ()) (TyLam () y (Type ()) $ TyVar () y))
                [integer2, integer2]
    integer2 @?= integer2'

test_normalizeTypesInIdempotent :: Property
test_normalizeTypesInIdempotent = property . hoist (pure . runQuote) $ do
    termNormTypes <- forAllT $ runAstGen genTerm >>= normalizeTypesIn
    termNormTypes' <- normalizeTypesIn termNormTypes
    termNormTypes === termNormTypes'

test_typeNormalization :: TestTree
test_typeNormalization =
    testGroup "typeNormalization"
        [ testCase     "appAppLamLam"               test_appAppLamLam
        , testProperty "normalizeTypesInIdempotent" test_normalizeTypesInIdempotent
        ]
