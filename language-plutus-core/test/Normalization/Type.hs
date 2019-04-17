{-# LANGUAGE OverloadedStrings #-}

module Normalization.Type
    ( test_typeNormalization
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Generators.AST
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Normalize
import           PlutusPrelude                      hiding (hoist)

import           Codec.Serialise
import           Control.Monad.Morph                (hoist)
import qualified Data.ByteString.Lazy               as BSL

import           Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

test_normalizer :: IO ()
test_normalizer = do
    (Program _ _ term) <- deserialise <$> BSL.readFile "test/deserialise/invalid.plci"
    let normTerm :: Term TyName Name ()
        normTerm = runQuote $ normalizeTypesFullIn term
        nonError :: Either (Error ()) a -> IO ()
        nonError = (@?= True) . isRight
    nonError (checkTerm normTerm)

test_appAppLamLam :: IO ()
test_appAppLamLam = do
    let integer2 = TyApp () (TyBuiltin () TyInteger) $ TyInt () 2
        Normalized integer2' = runQuote $ do
            x <- freshTyName () "x"
            y <- freshTyName () "y"
            normalizeTypeFull $ mkIterTyApp ()
                (TyLam () x (Type ()) (TyLam () y (Type ()) $ TyVar () y))
                [integer2, integer2]
    integer2 @?= integer2'

test_normalizeTypesInIdempotent :: Property
test_normalizeTypesInIdempotent = property . hoist (pure . runQuote) $ do
    term <- forAll genTerm
    mayTermNormTypes <- normalizeTypesGasIn (Gas 100) term
    case mayTermNormTypes of
        Nothing            -> return ()
        Just termNormTypes -> do
            termNormTypes' <- normalizeTypesFullIn termNormTypes
            termNormTypes === termNormTypes'

test_typeNormalization :: TestTree
test_typeNormalization =
    testGroup "typeNormalization"
        [ testCase     "appAppLamLam"               test_appAppLamLam
        , testProperty "normalizeTypesInIdempotent" test_normalizeTypesInIdempotent
        , testCase     "plutusTxOutput"             test_normalizer
        ]
