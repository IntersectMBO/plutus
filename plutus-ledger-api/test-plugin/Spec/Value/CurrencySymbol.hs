{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Spec.Value.CurrencySymbol where

import Data.ByteString (ByteString)
import PlutusCore (DefaultFun, DefaultUni, NamedDeBruijn, someValue)
import PlutusLedgerApi.V1 (CurrencySymbol (..))
import PlutusTx (CompiledCode, getPlcNoAnn)
import PlutusTx.TH (compile)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import UntypedPlutusCore (Program (_progTerm), Term (Constant))

tests :: TestTree
tests = testGroup "IsString CurrencySymbol" [test_CurrencySymbol_IsString_Raw]

test_CurrencySymbol_IsString_Raw :: TestTree
test_CurrencySymbol_IsString_Raw = testCase "Raw" do
  let expectedTerm = Constant () (someValue ("\xBA\xBE" :: ByteString))
  term $$(compile [||CurrencySymbol "\xBA\xBE"||]) @?= expectedTerm

term :: CompiledCode a -> Term NamedDeBruijn DefaultUni DefaultFun ()
term = _progTerm . getPlcNoAnn
