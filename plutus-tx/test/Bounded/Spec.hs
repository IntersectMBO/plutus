{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Bounded.Spec (boundedTests) where

import PlutusTx.Bounded as Tx
import PlutusTx.Test.Golden
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit
import Prelude hiding (Eq (..), error)
import Prelude qualified as HS (Bounded (..), Eq (..), Show (..))

data SomeVeryLargeEnum
  = E1
  | E2
  | E3
  | E4
  | E5
  | E6
  | E7
  | E8
  | E9
  | E10
  deriving stock (HS.Eq, HS.Bounded, HS.Show)
deriveBounded ''SomeVeryLargeEnum

data SingleConstructor a = SingleConstructor Bool a ()
deriveBounded ''SingleConstructor

newtype PhantomADT e = PhantomADT ()
  deriving stock (HS.Eq, HS.Bounded, HS.Show)
deriveBounded ''PhantomADT

boundedTests :: TestTree
boundedTests =
  let
   in testGroup
        "PlutusTx.Enum tests"
        [ testCase "conforms to haskell" $ (Tx.minBound @SomeVeryLargeEnum, Tx.maxBound @SomeVeryLargeEnum) @?= (HS.minBound, HS.maxBound)
        , testCase "phantom" $ Tx.minBound @(PhantomADT _) @?= HS.minBound
        , runTestNested
            ["test", "Bounded", "Golden"]
            [ $(goldenCodeGen "SomeVeryLargeEnum" (deriveBounded ''SomeVeryLargeEnum))
            , $(goldenCodeGen "Unit" (deriveBounded ''()))
            , $(goldenCodeGen "Ordering" (deriveBounded ''Ordering))
            , $(goldenCodeGen "SingleConstructor" (deriveBounded ''SingleConstructor))
            , $(goldenCodeGen "PhantomADT" (deriveBounded ''PhantomADT))
            ]
        ]
