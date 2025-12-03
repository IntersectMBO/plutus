{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module Ord.Spec (ordTests) where

import Test.Tasty
import Test.Tasty.HUnit
import PlutusTx.Test.Golden
import PlutusTx.Enum as Tx
import PlutusTx.Eq
import PlutusTx.Ord as Tx
import Test.Tasty.Extras
import Prelude as HS
import PlutusTx.Builtins

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
  deriving stock (HS.Eq, HS.Show, HS.Bounded)
deriveEnum ''SomeVeryLargeEnum
deriveEq ''SomeVeryLargeEnum
deriveOrd ''SomeVeryLargeEnum

data SomeProduct = SomeProduct Integer BuiltinByteString Bool (Either () ())
deriveEq ''SomeProduct
deriveOrd ''SomeProduct

unitTests :: TestTree
unitTests = testGroup "PlutusTx.Ord unit tests" $
  let l = Tx.enumFromTo @SomeVeryLargeEnum HS.minBound HS.maxBound
      l' = HS.tail l
  in [ testCase "enum series is lt" $ zipWith Tx.compare l l' @?= (take (length l') [LT,LT ..])
     , testCase "product1" $ SomeProduct 1 (encodeUtf8 "a") True (Right ()) Tx.> SomeProduct 0 (encodeUtf8 "a") True (Right ()) @? "product1 failed"
     , testCase "product2" $ SomeProduct 1 (encodeUtf8 "a") True (Right ()) Tx.< SomeProduct 1 (encodeUtf8 "b") True (Left ()) @? "product2 failed"
     , testCase "product3" $ SomeProduct 1 (encodeUtf8 "a") True (Right ()) Tx.> SomeProduct 1 (encodeUtf8 "a") False (Left ()) @? "product3 failed"
     , testCase "product3" $ SomeProduct 1 (encodeUtf8 "a") True (Left ()) Tx.< SomeProduct 1 (encodeUtf8 "a") True (Right ()) @? "product4 failed"
     ]

goldenTests :: TestTree
goldenTests=
  runTestNested
  ["test", "Ord", "Golden"]
    [ $(goldenCodeGen "SomeVeryLargeEnum" (deriveOrd ''SomeVeryLargeEnum))
    , $(goldenCodeGen "SomeProduct" (deriveOrd ''SomeProduct))
    ]

ordTests :: TestTree
ordTests =
  testGroup
    "PlutusTx.Ord tests"
    [unitTests, goldenTests]
