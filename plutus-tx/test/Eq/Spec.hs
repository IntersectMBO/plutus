{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Eq.Spec (eqTests) where

import Control.Exception
import PlutusTx.Bool qualified as Tx
import PlutusTx.Builtins as Tx
import PlutusTx.Eq as Tx
import PlutusTx.Ratio (Rational)
import PlutusTx.Test.Golden
import PlutusTx.These (These)
import Test.Tasty.Extras

import Data.Either

import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (Eq (..), Rational, error)
import Prelude qualified as HS (Eq (..))

data SomeVoid
  deriving stock (HS.Eq)
deriveEq ''SomeVoid

data SomeLargeADT a b c d e
  = SomeLargeADT1 Integer a Tx.Bool b c d
  | SomeLargeADT2
  | SomeLargeADT3 {f1 :: e, f2 :: e, _f3 :: e, _f4 :: e, _f5 :: e}
  deriving stock (HS.Eq)
deriveEq ''SomeLargeADT

newtype PhantomADT e = PhantomADT ()
  deriving stock (HS.Eq)
deriveEq ''PhantomADT

newtype MyNewtype = MyNewtype Integer
  deriving stock (HS.Eq)
deriveEq ''MyNewtype

data Tree a
  = Leaf a
  | Node (Tree a) (Tree a)
  deriving stock (HS.Eq)
deriveEq ''Tree

unitTests :: TestTree
unitTests =
  let v1 :: SomeLargeADT () BuiltinString () () () = SomeLargeADT1 1 () Tx.True "foobar" () ()
      v2 :: SomeLargeADT () () () () () = SomeLargeADT2
      v3 :: SomeLargeADT () () () () Integer = SomeLargeADT3 1 2 3 4 5
      v3Error1 = v3 {f1 = 0, f2 = error ()} -- mismatch comes first, error comes later
      v3Error2 = v3 {f1 = error (), f2 = 0} -- error comes first, mismatch later
      v4 :: SomeVoid = undefined
      v5 = MyNewtype 42
      v6 = MyNewtype 99
      v7 :: Tree Integer = Leaf 1
      v8 :: Tree Integer = Node (Leaf 1) (Leaf 2)
      v9 :: Tree Integer = Node (Leaf 1) (Node (Leaf 2) (Leaf 3))
   in testGroup
        "PlutusTx.Eq unit tests"
        [ testCase "reflexive1" $ (v1 Tx.== v1) @?= (v1 HS.== v1)
        , testCase "reflexive2" $ (v2 Tx.== v2) @?= (v2 HS.== v2)
        , testCase "reflexive3" $ (v3 Tx.== v3) @?= (v3 HS.== v3)
        , -- polymorphic phantom types, no type annotation is needed
          testCase "phantom" $ (PhantomADT () Tx.== PhantomADT ()) @?= (PhantomADT () HS.== PhantomADT ())
        , testCase "shortcircuit" $ (v3 Tx.== v3Error1) @?= (v3 Tx.== v3Error1) -- should not throw an error
        , testCase "throws" $ try @SomeException (evaluate $ v3 Tx.== v3Error2) >>= assertBool "did not throw error" . isLeft -- should throw error
        , testCase "void" $ (v4 Tx.== v4) @?= (v4 HS.== v4)
        , testCase "newtype-eq" $ (v5 Tx.== v5) @?= (v5 HS.== v5)
        , testCase "newtype-neq" $ (v5 Tx.== v6) @?= (v5 HS.== v6)
        , testCase "recursive-leaf" $ (v7 Tx.== v7) @?= (v7 HS.== v7)
        , testCase "recursive-node" $ (v8 Tx.== v8) @?= (v8 HS.== v8)
        , testCase "recursive-nested" $ (v9 Tx.== v9) @?= (v9 HS.== v9)
        , testCase "recursive-different" $ (v7 Tx.== v8) @?= (v7 HS.== v8)
        ]

goldenTests :: TestTree
goldenTests =
  runTestNested
    ["test", "Eq", "Golden"]
    [ $(goldenCodeGen "SomeLargeADT" (deriveEq ''SomeLargeADT))
    , $(goldenCodeGen "PhantomADT" (deriveEq ''PhantomADT))
    , $(goldenCodeGen "MyNewtype" (deriveEq ''MyNewtype))
    , $(goldenCodeGen "Tree" (deriveEq ''Tree))
    , -- Types from PlutusTx modules that use deriveEq
      $(goldenCodeGen "Rational" (deriveEq ''Rational))
    , $(goldenCodeGen "These" (deriveEq ''These))
    ]

eqTests :: TestTree
eqTests =
  testGroup
    "PlutusTx.Eq tests"
    [unitTests, goldenTests]
