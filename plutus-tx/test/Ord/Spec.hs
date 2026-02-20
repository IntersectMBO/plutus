{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Ord.Spec (ordTests) where

import PlutusTx.Builtins
import PlutusTx.Enum as Tx
import PlutusTx.Eq
import PlutusTx.Ord as Tx
import PlutusTx.Test.Golden
import PlutusTx.These (These)
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit
import Prelude as HS

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

newtype PhantomADT e = PhantomADT ()
  deriving stock (HS.Eq, HS.Show)
deriveEq ''PhantomADT
deriveOrd ''PhantomADT

newtype MyNewtype = MyNewtype Integer
  deriving stock (HS.Eq, HS.Ord)
deriveEq ''MyNewtype
deriveOrd ''MyNewtype

data SomeLargeADT a b c d e
  = SomeLargeADT1 Integer a Bool b c d
  | SomeLargeADT2
  | SomeLargeADT3 {_f1 :: e, _f2 :: e, _f3 :: e, _f4 :: e, _f5 :: e}
  deriving stock (HS.Eq, HS.Ord)
deriveEq ''SomeLargeADT
deriveOrd ''SomeLargeADT

data Tree a
  = Leaf a
  | Node (Tree a) (Tree a)
  deriving stock (HS.Eq, HS.Ord)
deriveEq ''Tree
deriveOrd ''Tree

data SomeVoid
  deriving stock (HS.Eq, HS.Ord)
deriveEq ''SomeVoid
deriveOrd ''SomeVoid

unitTests :: TestTree
unitTests =
  testGroup "PlutusTx.Ord unit tests" $
    let l = Tx.enumFromTo @SomeVeryLargeEnum HS.minBound HS.maxBound
        l' = HS.drop 1 l
        v1 :: SomeLargeADT () BuiltinByteString () () Integer
        v1 = SomeLargeADT3 1 2 3 4 5
        v2 :: SomeLargeADT () BuiltinByteString () () Integer
        v2 = SomeLargeADT3 1 2 3 4 6
        v3 :: SomeLargeADT () BuiltinByteString () () Integer
        v3 = SomeLargeADT2
     in [ testCase "enum series is lt" $ zipWith Tx.compare l l' @?= (take (length l') [LT, LT ..])
        , testCase "product1" $ SomeProduct 1 (encodeUtf8 "a") True (Right ()) Tx.> SomeProduct 0 (encodeUtf8 "a") True (Right ()) @? "product1 failed"
        , testCase "product2" $ SomeProduct 1 (encodeUtf8 "a") True (Right ()) Tx.< SomeProduct 1 (encodeUtf8 "b") True (Left ()) @? "product2 failed"
        , testCase "product3" $ SomeProduct 1 (encodeUtf8 "a") True (Right ()) Tx.> SomeProduct 1 (encodeUtf8 "a") False (Left ()) @? "product3 failed"
        , testCase "product4" $ SomeProduct 1 (encodeUtf8 "a") True (Left ()) Tx.< SomeProduct 1 (encodeUtf8 "a") True (Right ()) @? "product4 failed"
        , testCase "newtype-lt" $ MyNewtype 1 Tx.< MyNewtype 2 @? "newtype-lt failed"
        , testCase "newtype-eq" $ Tx.compare (MyNewtype 42) (MyNewtype 42) @?= EQ
        , testCase "large-adt-same-con" $ Tx.compare v1 v2 @?= LT
        , testCase "large-adt-diff-con" $ Tx.compare v3 v1 @?= LT
        , testCase "tree-leaf-lt" $ Tx.compare (Leaf (1 :: Integer)) (Leaf 2) @?= LT
        , testCase "tree-node" $ Tx.compare (Node (Leaf (1 :: Integer)) (Leaf 2)) (Node (Leaf 1) (Leaf 3)) @?= LT
        , testCase "tree-leaf-vs-node" $ Tx.compare (Leaf (1 :: Integer)) (Node (Leaf 0) (Leaf 0)) @?= LT
        , testCase "void" $ (undefined :: SomeVoid) `Tx.compare` undefined @=? (undefined :: SomeVoid) `HS.compare` undefined
        ]

goldenTests :: TestTree
goldenTests =
  runTestNested
    ["test", "Ord", "Golden"]
    [ $(goldenCodeGen "SomeVeryLargeEnum" (deriveOrd ''SomeVeryLargeEnum))
    , $(goldenCodeGen "SomeProduct" (deriveOrd ''SomeProduct))
    , $(goldenCodeGen "PhantomADT" (deriveOrd ''PhantomADT))
    , $(goldenCodeGen "MyNewtype" (deriveOrd ''MyNewtype))
    , $(goldenCodeGen "SomeLargeADT" (deriveOrd ''SomeLargeADT))
    , $(goldenCodeGen "Tree" (deriveOrd ''Tree))
    , -- Types from PlutusTx modules that use deriveOrd
      $(goldenCodeGen "These" (deriveOrd ''These))
    ]

ordTests :: TestTree
ordTests =
  testGroup
    "PlutusTx.Ord tests"
    [unitTests, goldenTests]
