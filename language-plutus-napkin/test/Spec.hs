{-# LANGUAGE OverloadedStrings #-}

module Main ( main
            , genPosn
            ) where

import           Data.Foldable       (fold)
import           Hedgehog
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range
import           Language.PlutusCore
import           Test.Tasty
import           Test.Tasty.HUnit

genPosn :: MonadGen m => m AlexPosn
genPosn = AlexPn <$> int' <*> int' <*> int'
    where int' = Gen.int (Range.linear 0 1000)

-- TODO generate random trees, print them, parse the original result (hopefully)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testCase "builtin" $ fold
    [ format "(program 0.1.0 [(builtin addInteger) x y])" @?= Right "(program 0.1.0 [ (builtin addInteger) x y ])"
    , format "(program 0.1.0 [(builtin addInteger) +1 y])" @?= Right "(program 0.1.0 [ (builtin addInteger) 1 y ])"
    , format "(program 0.1.0 doesn't)" @?= Right "(program 0.1.0 doesn't)"
    ]
