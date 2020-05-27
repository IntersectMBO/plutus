module Data.Foldable.ExtraTests
  ( all
  ) where

import Prelude
import Data.Array (replicate, length)
import Data.Foldable (foldMap, null)
import Data.Foldable.Extra (interleave, countConsecutive)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.List as List
import Data.NonEmpty ((:|))
import Data.Tuple (uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Test.QuickCheck (class Arbitrary, arbitrary, (<=?), (===))
import Test.QuickCheck.Gen (Gen, frequency, suchThat)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)

all :: TestSuite
all =
  suite "Data.Foldable.Extra" do
    interleaveTests
    countConsecutiveTests

interleaveTests :: TestSuite
interleaveTests = do
  suite "interleave" do
    test "Empty arrays are unchanged" do
      quickCheck do
        sep <- arbitrary :: Gen String
        pure $ interleave sep [] === []
    test "Singleton arrays are unchanged" do
      quickCheck do
        sep <- arbitrary :: Gen String
        x <- arbitrary
        pure $ interleave sep [ x ] === [ x ]
    test "Non-empty arrays increase their length by (2n - 1)" do
      quickCheck do
        sep <- arbitrary :: Gen String
        xs :: Array String <- arbitrary `suchThat` (not <<< null)
        pure $ length (interleave sep xs) === (2 * length xs) - 1
    test "Simple concrete example" do
      equal
        [ 1, 0, 2, 0, 3 ]
        (interleave 0 [ 1, 2, 3 ])

data Msg
  = Startup
  | Heartbeat
  | Healthy Boolean
  | Shutdown

derive instance eqMsg :: Eq Msg

derive instance genericMsg :: Generic Msg _

instance showMsg :: Show Msg where
  show = genericShow

instance arbitraryMsg :: Arbitrary Msg where
  arbitrary =
    frequency
      $ (20.0 /\ pure Heartbeat)
      :| List.fromFoldable
          [ 1.0 /\ pure Startup
          , 3.0 /\ pure (Healthy true)
          , 2.0 /\ pure (Healthy false)
          , 1.0 /\ pure Shutdown
          ]

countConsecutiveTests :: TestSuite
countConsecutiveTests = do
  suite "countConsecutive" do
    test "Empty." do
      equal
        (countConsecutive [])
        ([] :: Array (Int /\ String))
    test "The resulting sequence is never larger." do
      quickCheck \msgs ->
        length (countConsecutive msgs) <=? length (msgs :: Array Msg)
    test "We can reconstruct the original sequence by replicating each message the given number of times.." do
      quickCheck \msgs ->
        let
          counted :: Array (Int /\ Msg)
          counted = countConsecutive msgs
        in
          msgs === foldMap (uncurry replicate) counted
    test "Concrete example." do
      equal
        ( countConsecutive
            [ Startup
            , Heartbeat
            , Heartbeat
            , Heartbeat
            , Heartbeat
            , Heartbeat
            , Healthy true
            , Healthy true
            , Heartbeat
            , Heartbeat
            , Heartbeat
            , Shutdown
            ]
        )
        [ 1 /\ Startup
        , 5 /\ Heartbeat
        , 2 /\ Healthy true
        , 3 /\ Heartbeat
        , 1 /\ Shutdown
        ]
