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

versionEq :: Version a -> Version a -> Bool
versionEq (Version _ i j k) (Version _ i' j' k') =
    and (zipWith (==) [i, j, k] [i', j', k'])

programEq :: Program a -> Program a -> Bool
programEq (Program _ v t) (Program _ v' t') = versionEq v v' && termEq t t'

builtinEq :: Builtin a -> Builtin a -> Bool
builtinEq (BuiltinInt _ s i) (BuiltinInt _ s' i') = s == s' && i == i'
builtinEq (BuiltinSize _ s) (BuiltinSize _ s')    = s == s'
builtinEq (BuiltinBS _ s b) (BuiltinBS _ s' b')   = s == s' && b == b'
builtinEq (BuiltinName _ n) (BuiltinName _ n')    = n == n'
builtinEq _ _                                     = False

termEq :: Term a -> Term a -> Bool
termEq (Builtin _ b) (Builtin _ b') = builtinEq b b'
termEq (Var _ n) (Var _ n')         = n == n'
termEq _ _                          = undefined

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
