{-# LANGUAGE OverloadedStrings #-}

module Spec.ScriptDecodeError where

import Codec.Extras.SerialiseViaFlat (DeserialiseFailureInfo (..), DeserialiseFailureReason (..))
import PlutusCore.Version (plcVersion100)
import PlutusLedgerApi.Common (ScriptDecodeError (..))
import PlutusLedgerApi.Common.Versions (PlutusLedgerLanguage (..), changPV, vasilPV)
import Prettyprinter (Pretty (pretty))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@?=))

tests :: TestTree
tests =
  testGroup
    "ScriptDecodeError pretty-printing"
    [ testCase
        "CBORDeserialiseError"
        prettyCBORDeserialiseError
    , testCase
        "RemainderError"
        prettyRemainderError
    , testCase
        "LedgerLanguageNotAvailableError"
        prettyLedgerLanguageNotAvailableError
    , testCase
        "PlutusCoreLanguageNotAvailableError"
        prettyPlutusCoreLanguageNotAvailableError
    ]

prettyCBORDeserialiseError :: Assertion
prettyCBORDeserialiseError =
  show (pretty err)
    @?= "Failed to deserialise a script: CBOR deserialisation failed \
        \at the offset 12345 for the following reason: reached the end \
        \of input while more data was expected."
  where
    err =
      CBORDeserialiseError
        DeserialiseFailureInfo {dfOffset = 12345, dfReason = EndOfInput}

prettyRemainderError :: Assertion
prettyRemainderError =
  show (pretty (RemainderError "bytes"))
    @?= "Script was successfully deserialised, but 5 more bytes were \
        \encountered after the script's position."

prettyLedgerLanguageNotAvailableError :: Assertion
prettyLedgerLanguageNotAvailableError =
  show (pretty err)
    @?= "Your script has a Plutus Ledger Language version of PlutusV2. \
        \This is not yet supported by the current major protocol version 7. \
        \The major protocol version that introduces this \
        \Plutus Ledger Language is 9."
  where
    err =
      LedgerLanguageNotAvailableError
        { sdeAffectedLang = PlutusV2
        , sdeIntroPv = changPV
        , sdeThisPv = vasilPV
        }

prettyPlutusCoreLanguageNotAvailableError :: Assertion
prettyPlutusCoreLanguageNotAvailableError =
  show (pretty err)
    @?= "Your script has a Plutus Core version of 1.0.0. \
        \This is not supported in PlutusV2 and major protocol version 7."
  where
    err =
      PlutusCoreLanguageNotAvailableError
        { sdeAffectedVersion = plcVersion100
        , sdeThisLang = PlutusV2
        , sdeThisPv = vasilPV
        }
