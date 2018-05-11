{-# LANGUAGE OverloadedStrings #-}

module Main ( main
            , genPosn
            , programEq
            ) where

import           Data.Foldable       (fold, traverse_)
import           Hedgehog            hiding (Var)
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range
import           Language.PlutusCore
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

main :: IO ()
main = traverse_ defaultMain [tests, propertyTests]

genPosn :: MonadGen m => m AlexPosn
genPosn = AlexPn <$> int' <*> int' <*> int'
    where int' = Gen.int (Range.linear 0 1000)

emptyPosn :: AlexPosn
emptyPosn = AlexPn 0 0 0

termEq :: Program AlexPosn -> Program AlexPosn -> Bool
termEq p p' = nullPosn p == nullPosn p'
    where nullPosn = fmap (pure emptyPosn)

propParser :: Property
propParser = property $ do
    xs <- forAll genPosn
    xs === xs

propertyTests :: TestTree
propertyTests = testGroup "property tests"
    [ testProperty "property test" propParser
    ]

tests :: TestTree
tests = testCase "builtin" $ fold
    [ format "(program 0.1.0 [(builtin addInteger) x y])" @?= Right "(program 0.1.0 [ (builtin addInteger) x y ])"
    , format "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0 doesn't)"
    ]
