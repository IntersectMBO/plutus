{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
-- needed since we don't support polymorphic phantom types
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Eq.Spec (eqTests) where

import Control.Exception
import PlutusTx.Bool qualified as Tx
import PlutusTx.Builtins as Tx
import PlutusTx.Eq as Tx
import PlutusTx.Test.Golden
import Test.Tasty.Extras

import Data.Either

import Test.Tasty
import Test.Tasty.HUnit
import Prelude hiding (Eq (..), error)
import Prelude qualified as HS (Eq (..))

data SomeLargeADT a b c d e
  = SomeLargeADT1 Integer a Tx.Bool b c d
  | SomeLargeADT2
  | SomeLargeADT3 {f1 :: e, f2 :: e, _f3 :: e, _f4 :: e, _f5 :: e}
  deriving stock (HS.Eq)
deriveEq ''SomeLargeADT

newtype PhantomADT e = PhantomADT ()
  deriving stock (HS.Eq)
deriveEq ''PhantomADT

unitTests :: TestTree
unitTests =
  let v1 :: SomeLargeADT () BuiltinString () () () = SomeLargeADT1 1 () Tx.True "foobar" () ()
      v2 :: SomeLargeADT () () () () () = SomeLargeADT2
      v3 :: SomeLargeADT () () () () Integer = SomeLargeADT3 1 2 3 4 5
      v3Error1 = v3 {f1 = 0, f2 = error ()} -- mismatch comes first, error comes later
      v3Error2 = v3 {f1 = error (), f2 = 0} -- error comes first, mismatch later
   in testGroup
        "PlutusTx.Eq unit tests"
        [ testCase "reflexive1" $ (v1 Tx.== v1) @?= (v1 HS.== v1)
        , testCase "reflexive2" $ (v2 Tx.== v2) @?= (v2 HS.== v2)
        , testCase "reflexive3" $ (v3 Tx.== v3) @?= (v3 HS.== v3)
        , -- currently does not work with polymorphic phantom types, remove the type annotation when support is added
          testCase "phantom" $ (PhantomADT @() () Tx.== PhantomADT ()) @?= (PhantomADT () HS.== PhantomADT ())
        , testCase "shortcircuit" $ (v3 Tx.== v3Error1) @?= (v3 Tx.== v3Error1) -- should not throw an error
        , testCase "throws" $ try @SomeException (evaluate $ v3 Tx.== v3Error2) >>= assertBool "did not throw error" . isLeft -- should throw erro
        ]

goldenTests :: TestTree
goldenTests =
  runTestNested
    ["test", "Eq", "Golden"]
    [ $(goldenCodeGen "SomeLargeADT" (deriveEq ''SomeLargeADT))
    , $(goldenCodeGen "PhantomADT" (deriveEq ''PhantomADT))
    ]

eqTests :: TestTree
eqTests =
  testGroup
    "PlutusTx.Eq tests"
    [unitTests, goldenTests]
