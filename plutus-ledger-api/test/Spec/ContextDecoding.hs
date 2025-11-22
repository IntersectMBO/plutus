{-# LANGUAGE TypeApplications #-}

module Spec.ContextDecoding where

import Codec.Serialise qualified as S
import Data.ByteString.Lazy as BSL
import Data.Maybe
import PlutusCore.Data
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3
import PlutusTx.IsData
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "context decoding" [test_v1Context]

test_v1Context :: TestTree
test_v1Context = testCase "v1context" $ do
  input <- BSL.readFile "test/Spec/v1-context-data"
  let (d :: Data) = S.deserialise input
  assertBool
    "can't parse as V1 context"
    (isJust $ fromBuiltinData @V1.ScriptContext (V1.BuiltinData d))
  -- Note, these should return Nothing and not throw
  assertBool
    "can parse as V2 context"
    (isNothing $ fromBuiltinData @V2.ScriptContext (V2.BuiltinData d))
  assertBool
    "can parse as V3 context"
    (isNothing $ fromBuiltinData @V3.ScriptContext (V3.BuiltinData d))
