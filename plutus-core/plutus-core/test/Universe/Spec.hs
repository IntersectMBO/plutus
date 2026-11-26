{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module Universe.Spec (tests) where

import Control.DeepSeq (force)
import Control.Exception (ErrorCall, evaluate, try)
import Data.ByteString qualified as BS
import Data.Hashable (hashWithSalt)
import Data.Text qualified as Text
import Data.Word (Word8)
import PlutusCore
import PlutusCore.Flat qualified as Flat
import Test.Tasty
import Test.Tasty.HUnit

type Constant = SomeValueOf DefaultUni

assertBottom :: a -> Assertion
assertBottom x = do
  result <- try @ErrorCall (evaluate x >> pure ())
  case result of
    Left _ -> pure ()
    Right () -> assertFailure "Expected an undefined tag or payload to be forced"

tests :: TestTree
tests =
  testGroup
    "Universe constants"
    [ testCase "equality compares both the type and the payload" $ do
        (someValue (1 :: Integer) :: Constant) @?= someValue (1 :: Integer)
        assertBool "different payloads" $
          (someValue (1 :: Integer) :: Constant) /= someValue (2 :: Integer)
        assertBool "different element types in empty lists" $
          (someValue ([] :: [Integer]) :: Constant) /= someValue ([] :: [Bool])
    , testCase "hashing preserves the tag and payload hash" $
        hashWithSalt 42 (someValue ([1, 2] :: [Integer]) :: Constant)
          @?= hashWithSalt
            42
            (SomeTypeIn (DefaultUniList DefaultUniInteger), [1, 2] :: [Integer])
    , testCase "Show prints the constructor with correct precedence" $ do
        let value = someValue (-1 :: Integer) :: Constant
        show value @?= "SomeValueOf DefaultUniInteger (-1)"
        showsPrec 10 value "suffix" @?= "SomeValueOf DefaultUniInteger (-1)suffix"
        showsPrec 11 value "suffix" @?= "(SomeValueOf DefaultUniInteger (-1))suffix"
        show (someValue ([1, -2] :: [Integer]) :: Constant)
          @?= "SomeValueOf (DefaultUniApply DefaultUniProtoList DefaultUniInteger) [1,-2]"
        show (someValue (False, 3 :: Integer) :: Constant)
          @?= "SomeValueOf (DefaultUniApply (DefaultUniApply DefaultUniProtoPair DefaultUniBool) \
              \DefaultUniInteger) (False,3)"
    , testCase "construction forces the tag" $
        assertBottom (SomeValueOf (error "tag") (0 :: Integer) :: Constant)
    , testCase "construction forces the payload" $
        assertBottom (SomeValueOf DefaultUniInteger (error "payload"))
    , testCase "construction only forces the payload to WHNF" $ do
        _ <- evaluate (someValue [error "element" :: Integer] :: Constant)
        pure ()
    , testCase "NFData forces the nested payload" $
        assertBottom (force (someValue [error "element" :: Integer] :: Constant))
    , testGroup
        "Flat encoding compatibility"
        [ testCase label $ do
            Flat.flat value @?= BS.pack bytes
            Flat.unflat (BS.pack bytes) @?= Right value
        | (label, value, bytes) <- encodingFixtures
        ]
    ]

-- These bytes were captured from the previous Some (ValueOf DefaultUni) representation.
encodingFixtures :: [(String, Constant, [Word8])]
encodingFixtures =
  [ ("False", someValue False, [161])
  , ("True", someValue True, [163])
  , ("unit", someValue (), [153])
  , ("zero", someValue (0 :: Integer), [128, 1])
  , ("negative integer", someValue (-129 :: Integer), [130, 4, 9])
  , ("bytestring", someValue (BS.pack [0, 127, 255]), [137, 3, 0, 127, 255, 0, 1])
  , ("UTF-8 text", someValue (Text.pack "λ"), [145, 2, 206, 187, 0, 1])
  , ("integer list", someValue ([1, -2] :: [Integer]), [189, 96, 129, 64, 193])
  , ("pair", someValue (False, 3 :: Integer), [189, 237, 72, 0, 193])
  ]
