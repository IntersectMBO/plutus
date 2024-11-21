{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}

module Spec.Value.TokenName where

import Data.ByteString (ByteString)
import Data.Text.Encoding as TE
import PlutusCore (DefaultFun, DefaultUni, NamedDeBruijn, someValue)
import PlutusLedgerApi.V1.Value (TokenName (..))
import PlutusTx (CompiledCode, getPlcNoAnn)
import PlutusTx.Builtins (unBuiltinByteStringUtf8)
import PlutusTx.TH (compile)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import UntypedPlutusCore (Program (_progTerm), Term (Constant))

tests :: TestTree
tests =
  testGroup
    "IsString TokenName"
    [ test_TokenName_IsString_Utf8
    , test_TokenName_IsString_Raw
    ]

test_TokenName_IsString_Utf8 :: TestTree
test_TokenName_IsString_Utf8 = testCase "UTF8-encoded" do
  term $$(compile [||TokenName (unBuiltinByteStringUtf8 "Имя Токена")||])
    @?= Constant () (someValue (TE.encodeUtf8 "Имя Токена"))

test_TokenName_IsString_Raw :: TestTree
test_TokenName_IsString_Raw = testCase "Raw" do
  let expectedTerm = Constant () (someValue ("\xBA\xBE" :: ByteString))
  assertBool "Raw byte TokenName" $
    term $$(compile [||TokenName "\xBA\xBE"||]) == expectedTerm
  assertBool "UTF8-encoded TokenName" $
    term $$(compile [||TokenName (unBuiltinByteStringUtf8 "\xBA\xBE")||])
      /= expectedTerm

term :: CompiledCode a -> Term NamedDeBruijn DefaultUni DefaultFun ()
term = _progTerm . getPlcNoAnn
