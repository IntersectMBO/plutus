{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Normalization.Type
  ( test_typeNormalization
  ) where

import PlutusCore
import PlutusCore.Check.Normal (isNormalType)
import PlutusCore.Generators.Hedgehog.AST
import PlutusCore.Generators.QuickCheck.Builtin (constantTypeTag)
import PlutusCore.MkPlc
import PlutusCore.Normalize
import PlutusCore.Test

import Control.Monad.Except (runExceptT)
import Control.Monad.Morph (hoist)
import Data.Functor (void)
import Data.Vector.Strict qualified as Strict

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
    , testGroup
        "built-in type heads"
        [ testCase "nested constant tags expand immediately" $ do
            let tag = DefaultUniList $ DefaultUniPair DefaultUniInteger $ DefaultUniArray DefaultUniBool
                ty = mkTyBuiltinOf () tag :: Type TyName DefaultUni ()
                expected =
                  TyApp () (mkTyBuiltin @_ @[] ()) $
                    TyApp () (TyApp () (mkTyBuiltin @_ @(,) ()) (mkTyBuiltin @_ @Integer ())) $
                      TyApp () (mkTyBuiltin @_ @Strict.Vector ()) (mkTyBuiltin @_ @Bool ())
            ty @?= expected
            isNormalType ty @?= True
            runQuote (normalizeType ty) @?= Normalized ty
            constantTypeTag ty @?= Just (Some tag)
        , testCase "partially applied pair is normal" $ do
            let ty =
                  TyApp () (mkTyBuiltin @_ @(,) ()) (mkTyBuiltin @_ @Integer ())
                    :: Type TyName DefaultUni ()
            isNormalType ty @?= True
        , testCase "legacy parser syntax expands to normal types" $ do
            let parsed = runQuote $ runExceptT $ parseType "(con (list (pair integer (array bool))))"
                expected =
                  mkTyBuiltinOf () $
                    DefaultUniList $
                      DefaultUniPair DefaultUniInteger $
                        DefaultUniArray DefaultUniBool
            case parsed of
              Left err -> assertFailure $ show err
              Right ty -> do
                void ty @?= expected
                isNormalType ty @?= True
        , testCase "applications outside the universe do not become constant tags" $ do
            let ty =
                  TyApp () (mkTyBuiltin @_ @[] ()) (TyVar () $ TyName $ Name "a" $ Unique 0)
                    :: Type TyName DefaultUni ()
            isNormalType ty @?= True
            constantTypeTag ty @?= Nothing
        , testCase "ill-kinded applications do not become constant tags" $ do
            let ty =
                  TyApp () (mkTyBuiltin @_ @Bool ()) (mkTyBuiltin @_ @Integer ())
                    :: Type TyName DefaultUni ()
            constantTypeTag ty @?= Nothing
        ]
    , testPropertyNamed
        "normalizeTypesInIdempotent"
        "normalizeTypesInIdempotent"
        test_normalizeTypesInIdempotent
    ]
