{-# LANGUAGE OverloadedStrings#-}

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
        testTyProp depth kind prop_checkKindCorrect
    , testCase "normalization preserves kinds" $
        testTyProp depth kind prop_normalizePreservesKind
    , testCase "normalization for generated types is sound" $
        testTyProp depth kind prop_normalizeTypeCorrect
    ]
  ]


-- |Property: Kind checker for generated types is sound.
prop_checkKindCorrect :: TyProp
prop_checkKindCorrect _ _ k tyQ = isSafe $ do
  ty <- liftQuote tyQ
  checkKind defOffChainConfig () ty k

-- |Property: Normalisation preserves kind.
prop_normalizePreservesKind :: TyProp
prop_normalizePreservesKind _ _ k tyQ = isSafe $ do
  ty <- liftQuote tyQ
  ty' <- unNormalized <$> normalizeTypeFull ty
  checkKind defOffChainConfig () ty' k

-- |Property: Normalisation for generated types is sound.
prop_normalizeTypeCorrect :: TyProp
prop_normalizeTypeCorrect kG tyG _ tyQ = eitherToCool . getResult $ do
  ty1 <- unNormalized <$> (normalizeTypeFull =<< liftQuote tyQ)
  ty2 <- toClosedType kG (normalizeTypeG tyG)
  return (ty1 == ty2)


-- * Helper functions

eitherToCool :: Either e Bool -> Cool
eitherToCool = either (const false) toCool

getResult :: ExceptT (Error ()) Quote a -> Either (Error ()) a
getResult = runQuote . runExceptT

-- |Check if the type/kind checker threw any errors.
isSafe :: ExceptT (Error ()) Quote () -> Cool
isSafe = toCool . isRight . runQuote . runExceptT
