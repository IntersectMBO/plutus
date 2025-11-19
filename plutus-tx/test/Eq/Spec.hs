{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module Eq.Spec (eqTests) where

import PlutusTx.Builtins as Tx
import PlutusTx.Bool qualified as Tx
import PlutusTx.Eq as Tx
import Control.Exception

import Data.Either

import Prelude hiding (Eq (..), error)
import Prelude qualified as HS (Eq (..),)
import Test.Tasty
import Test.Tasty.HUnit

data SomeLargeADT a b c d e =
  SomeLargeADT1 Integer a Tx.Bool b c d
  | SomeLargeADT2
  | SomeLargeADT3 { f1 :: e, f2 :: e, _f3 :: e, _f4 :: e, _f5 :: e }
  deriving stock HS.Eq
deriveEq ''SomeLargeADT

eqTests :: TestTree
eqTests =
  let v1 :: SomeLargeADT () BuiltinString () () () = SomeLargeADT1 1 () Tx.True "foobar" () ()
      v2 :: SomeLargeADT () () () () () = SomeLargeADT2
      v3 :: SomeLargeADT () () () () Integer = SomeLargeADT3 1 2 3 4 5
      v3Error1 = v3 { f1 = 0, f2 = error () } -- mismatch comes first, error comes later
      v3Error2 = v3 { f1 = error (), f2 = 0 } -- error comes first, mismatch later

  in testGroup
    "PlutusTx.Eq tests"
    [testCase "reflexive1" $ (v1 Tx.== v1) @?= (v1 HS.== v1)
    , testCase "reflexive2" $ (v2 Tx.== v2) @?= (v2 HS.== v2)
    , testCase "reflexive3" $ (v3 Tx.== v3) @?= (v3 HS.== v3)
    , testCase "shortcircuit" $ (v3 Tx.== v3Error1) @?= (v3 Tx.== v3Error1) -- should not throw an error
    , testCase "throws" $ try @SomeException (evaluate $ v3 Tx.== v3Error2) >>= assertBool "did not throw error" . isLeft -- should throw erro
    ]
