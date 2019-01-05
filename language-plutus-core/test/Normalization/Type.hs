{-# LANGUAGE OverloadedStrings #-}

module Normalization.Type
    ( test_typeNormalization
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Normalize

import           Generators

import           Control.Monad.Morph           (hoist)

import           Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

test_appAppLamLam :: IO ()
test_appAppLamLam = do
    let integer2 = TyApp () (TyBuiltin () TyInteger) $ TyInt () 2
        Normalized integer2' = runQuote $ do
            x <- freshTyName () "x"
            y <- freshTyName () "y"
            normalizeTypeDown $ mkIterTyApp ()
                (TyLam () x (Type ()) (TyLam () y (Type ()) $ TyVar () y))
                [integer2, integer2]
    integer2 @?= integer2'

test_normalizeTypesInIdempotent :: Property
test_normalizeTypesInIdempotent = property . hoist (pure . runQuote) $ do
    term <- forAll genTerm
    mayTermNormTypes <- liftQuote . runNormalizeTypeGasM (Gas 100) $ normalizeTypesIn term
    case mayTermNormTypes of
        Nothing            -> return ()
        Just termNormTypes -> do
            termNormTypes' <- liftQuote . runNormalizeTypeDownM $ normalizeTypesIn termNormTypes
            termNormTypes === termNormTypes'

test_typeNormalization :: TestTree
test_typeNormalization =
    testGroup "typeNormalization"
        [ testCase     "appAppLamLam"               test_appAppLamLam
        , testProperty "normalizeTypesInIdempotent" test_normalizeTypesInIdempotent
        ]
