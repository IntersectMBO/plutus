{-# LANGUAGE OverloadedStrings #-}

module Main ( main
            , genPosn
            , programEq
            ) where

import           Data.Foldable       (fold, traverse_)
import           Hedgehog
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range
import           Language.PlutusCore
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

main :: IO ()
main =
    traverse_ defaultMain [tests, propertyTests]

genPosn :: MonadGen m => m AlexPosn
genPosn = AlexPn <$> int' <*> int' <*> int'
    where int' = Gen.int (Range.linear 0 1000)

-- TODO generate random trees, print them, parse the original result (hopefully)

versionEq :: Version a -> Version a -> Bool
versionEq (Version _ i j k) (Version _ i' j' k') =
    and (zipWith (==) [i, j, k] [i', j', k'])

programEq :: Program a -> Program a -> Bool
programEq (Program _ v t) (Program _ v' t') = versionEq v v' && termEq t t'

-- TODO catamorphism?
termEq :: Term a -> Term a -> Bool
termEq _ = undefined

propParser :: Property
propParser = property $ do
    xs <- forAll genPosn
    xs === xs

propertyTests :: TestTree
propertyTests = testGroup "property tests" $
    [ testProperty "property test" propParser
    ]

tests :: TestTree
tests = testCase "builtin" $ fold
    [ format "(program 0.1.0 [(builtin addInteger) x y])" @?= Right "(program 0.1.0 [ (builtin addInteger) x y ])"
    , format "(program 0.1.0 [(builtin addInteger) +1 y])" @?= Right "(program 0.1.0 [ (builtin addInteger) 1 y ])"
    , format "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0 doesn't)"
    ]
