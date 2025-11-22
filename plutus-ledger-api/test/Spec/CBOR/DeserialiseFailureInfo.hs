{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RankNTypes #-}

module Spec.CBOR.DeserialiseFailureInfo (tests) where

import Codec.CBOR.Decoding qualified as CBOR
import Codec.CBOR.Read qualified as CBOR
import Codec.Extras.SerialiseViaFlat qualified as CBOR

import Data.Bifunctor
import Data.ByteString.Lazy qualified as LBS
import Prettyprinter (Pretty, pretty)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, testCase, (@=?), (@?=))

tests :: TestTree
tests =
  testGroup
    "cbor failure"
    [ testGroup
        "intepretation tests"
        [ testCase "end-of-input" $
            (CBOR.decodeBytes `failsWith` CBOR.EndOfInput) []
        , testCase "expected-bytes" $
            (CBOR.decodeBytes `failsWith` CBOR.ExpectedBytes) [0x5c]
        , testCase "other" $
            (CBOR.decodeBool `failsWith` CBOR.OtherReason "expected bool") [0x5c]
        ]
    , testGroup
        "pretty-printing"
        [ testCase "end-of-input" $
            renderPretty
              CBOR.DeserialiseFailureInfo
                { CBOR.dfOffset = 123425678900000
                , CBOR.dfReason = CBOR.EndOfInput
                }
              @?= "CBOR deserialisation failed at the offset 123425678900000 \
                  \for the following reason: reached the end of input \
                  \while more data was expected."
        , testCase "expected-bytes" $
            renderPretty
              CBOR.DeserialiseFailureInfo
                { CBOR.dfOffset = 123425678900000
                , CBOR.dfReason = CBOR.ExpectedBytes
                }
              @?= "CBOR deserialisation failed at the offset 123425678900000 \
                  \for the following reason: \
                  \the bytes inside the input are malformed."
        , testCase "other" $
            let reason = "expected bool"
             in renderPretty
                  CBOR.DeserialiseFailureInfo
                    { CBOR.dfOffset = 123425678900000
                    , CBOR.dfReason = CBOR.OtherReason reason
                    }
                  @?= "CBOR deserialisation failed at the offset 123425678900000 \
                      \for the following reason: "
                    <> reason
        ]
    ]
  where
    failsWith
      :: (Eq a, Show a)
      => (forall s. CBOR.Decoder s a)
      -> CBOR.DeserialiseFailureReason
      -> LBS.ByteString
      -> Assertion
    failsWith decoder reason inp =
      let res = CBOR.deserialiseFromBytes decoder inp
       in Left reason @=? first (CBOR.dfReason . CBOR.readDeserialiseFailureInfo) res

    renderPretty :: Pretty a => a -> String
    renderPretty = show . pretty
