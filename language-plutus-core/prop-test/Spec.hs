{-|
Description: Runs property based tests on generated PLC

Currently only generates types

-}
{-# LANGUAGE OverloadedStrings #-}

import           Language.PlutusCore
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.PropTest

import           Control.Monad.Except
import           Data.Coolean
import           Data.Either
import           Test.Tasty
import           Test.Tasty.HUnit

depth :: Int
depth = 10

kind :: Kind ()
kind = Type ()

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "all tests"
  [ testGroup "types"
    [ testCase "kind checker for generated types is sound" $
        testTyProp depth kind prop_checkKindSound
    , testCase "normalization preserves kinds" $
        testTyProp depth kind prop_normalizePreservesKind
    , testCase "normalization for generated types is sound" $
        testTyProp depth kind prop_normalizeTypeSound
    ]
  ]


-- |Property: Kind checker for generated types is sound.
prop_checkKindSound :: TyProp
prop_checkKindSound _ _ k tyQ = isSafe $ do
  ty <- liftQuote tyQ
  checkKind defConfig () ty k

-- |Property: Normalisation preserves kind.
prop_normalizePreservesKind :: TyProp
prop_normalizePreservesKind _ _ k tyQ = isSafe $ do
  ty <- liftQuote tyQ
  ty' <- unNormalized <$> normalizeType ty
  checkKind defConfig () ty' k

-- |Property: Normalisation for generated types is sound.
prop_normalizeTypeSound :: TyProp
prop_normalizeTypeSound kG tyG _ tyQ = isSafe $ do
  ty1 <- unNormalized <$> (normalizeType =<< liftQuote tyQ)
  ty2 <- toClosedType kG (normalizeTypeG tyG)
  return (ty1 == ty2)

-- |Check if the type/kind checker threw any errors.
isSafe :: ExceptT (Error DefaultUni a) Quote a -> Cool
isSafe = toCool . isRight . runQuote . runExceptT
