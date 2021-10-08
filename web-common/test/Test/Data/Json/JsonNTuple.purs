module Test.Data.Json.JsonNTuple where

import Prelude
import Control.Monad.Except (runExceptT)
import Data.Either (Either(..))
import Data.Json.JsonNTuple ((/\))
import Foreign (Foreign)
import Foreign.Class (decode, encode)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)

foreign import stringify :: Foreign -> String

foreign import jsonParse :: String -> Foreign

jsonNTupleTest :: TestSuite
jsonNTupleTest = do
  suite "encode" do
    test "Tuple" do
      equal
        "[1,\"2\"]"
        (stringify $ encode $ 1 /\ "2")
    test "Triple" do
      equal
        "[1,\"2\",true]"
        (stringify $ encode $ 1 /\ "2" /\ true)
    test "4-Tuple" do
      equal
        "[1,\"2\",true,4]"
        (stringify $ encode $ 1 /\ "2" /\ true /\ 4)
  suite "decode" do
    test "Tuple" do
      equal
        (pure $ Right $ 1 /\ "2")
        (runExceptT $ decode $ jsonParse "[1,\"2\"]")
    test "Triple" do
      equal
        (pure $ Right $ 1 /\ "2" /\ true)
        (runExceptT $ decode $ jsonParse "[1,\"2\",true]")
    test "4-Tuple" do
      equal
        (pure $ Right $ 1 /\ "2" /\ true /\ 4)
        (runExceptT $ decode $ jsonParse "[1,\"2\",true,4]")
