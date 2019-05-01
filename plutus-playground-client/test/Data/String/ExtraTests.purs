module Data.String.ExtraTests
       ( all
       ) where

import Prelude

import Data.String as String
import Data.String.Extra (abbreviate, leftPadTo, repeat, toHex)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)

all :: TestSuite
all =
  suite "Data.String.Extra" do
    abbreviateTests
    toHexTests
    leftPadToTests
    repeatTests

abbreviateTests :: TestSuite
abbreviateTests = do
  suite "abbreviate" do
    test "Always limits the string length" do
      quickCheck \str -> String.length (abbreviate str) <= 10
    test "Never affects the start of the string" do
      quickCheck \str ->
        String.take 5 str ==
        String.take 5 (abbreviate str)

toHexTests :: TestSuite
toHexTests = do
  suite "toHex" do
    test "A few examples" do
      equal "41" (toHex "A")
      equal "546573746572" (toHex "Tester")

leftPadToTests :: TestSuite
leftPadToTests = do
  suite "leftPadTo" do
    test "0 is identity" do
      quickCheck \prefix str -> str == leftPadTo 0 prefix str
    test "A few examples" do
      equal "0f" (leftPadTo 2 "0" "f")
      equal "  f" (leftPadTo 3 " " "f")
      equal "f" (leftPadTo 1 "0" "f")

repeatTests :: TestSuite
repeatTests = do
  suite "repeat" do
    test "0 is empty" do
      quickCheck \str -> repeat 0 str == ""
    test "A few examples" do
      equal "abcabcabc" (repeat 3 "abc")
      equal "TestTest" (repeat 2 "Test")
