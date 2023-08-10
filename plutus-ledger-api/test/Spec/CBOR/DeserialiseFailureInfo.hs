{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RankNTypes      #-}
module Spec.CBOR.DeserialiseFailureInfo (tests)
where

import Codec.CBOR.Decoding as CBOR
import Codec.CBOR.Extras as CBOR
import Codec.CBOR.Read as CBOR

import Data.Bifunctor
import Data.ByteString.Lazy qualified as LBS
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "cbor failure intepretation tests"
     [ testCase "end-of-input" $
         (CBOR.decodeBytes `failsWith` CBOR.EndOfInput) []
     , testCase "expected-bytes" $
         (CBOR.decodeBytes `failsWith` CBOR.ExpectedBytes) [0x5c]
     , testCase "other" $
         (CBOR.decodeBool `failsWith` CBOR.OtherReason "expected bool") [0x5c]
     ]
  where
    failsWith :: (Eq a, Show a)
              => (forall s. Decoder s a) -> DeserialiseFailureReason -> LBS.ByteString -> Assertion
    failsWith decoder reason inp =
        let res = CBOR.deserialiseFromBytes decoder inp
        in Left reason @=? first (CBOR.dfReason . readDeserialiseFailureInfo) res
