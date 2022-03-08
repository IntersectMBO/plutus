{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Main where

import DeBruijn.Spec (test_debruijn)
import Evaluation.Builtins (test_builtins)
import Evaluation.FreeVars (test_freevars)
import Evaluation.Golden (test_golden)
import Evaluation.Machines
import Transform.Simplify (test_simplify)

import Data.ByteString as BS
import Data.Either

import Test.Tasty
import Test.Tasty.HUnit

import PlutusCore.MkPlc qualified as UPLC
import UntypedPlutusCore qualified as UPLC

import Flat qualified
import Flat.Decoder qualified as Flat

main :: IO ()
main = defaultMain $ testGroup "Untyped Plutus Core"
    [ test_machines
    , test_builtins
    , test_budget
    , test_golden
    , test_tallying
    , test_simplify
    , test_deserializingBigConstants
    , test_debruijn
    , test_freevars
    ]

test_deserializingBigConstants :: TestTree
test_deserializingBigConstants = testGroup "64-byte deserialization limit"
    [ test_bigInteger
    , test_bigByteString
    , test_nested
    ]

type Term = UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ()

limitedDecoder :: Flat.Get Term
limitedDecoder = UPLC.decodeTerm (UPLC.Limit 64) (const True)

test_bigInteger :: TestTree
test_bigInteger = testCase "big integer" $ do
    let  -- A 64-byte integer
        justOver :: Integer
        justOver = 2 ^ (64 * 8 :: Integer)
        -- Something that flat actually encodes in under 64 bytes
        -- It's surprising that this is so much under 64 bytes of content...
        justUnder :: Integer
        justUnder = 2 ^ (55 * 8 :: Integer) - 1
        t1 :: Term
        t1 = UPLC.mkConstant () justOver
        t2 :: Term
        t2 = UPLC.mkConstant () justUnder
    assertBool "justOver" (isLeft $ Flat.unflatWith limitedDecoder (Flat.flat t1))
    assertBool "justUnder" (isRight $ Flat.unflatWith limitedDecoder (Flat.flat t2))

test_bigByteString :: TestTree
test_bigByteString = testCase "big bytestring" $ do
    let -- A 64-byte bytestring
        justOver :: ByteString
        justOver = BS.replicate 64 1
        -- Something that flat actually encodes in under 64 bytes
        -- It's surprising that this is so much under 64 bytes of content...
        justUnder :: ByteString
        justUnder = BS.replicate 60 1
        t1 :: Term
        t1 = UPLC.mkConstant () justOver
        t2 :: Term
        t2 = UPLC.mkConstant () justUnder
    assertBool "justOver" (isLeft $ Flat.unflatWith limitedDecoder (Flat.flat t1))
    assertBool "justUnder" (isRight $ Flat.unflatWith limitedDecoder (Flat.flat t2))

test_nested :: TestTree
test_nested = testCase "nested" $ do
    let  -- A 64-byte integer
        justOver :: Integer
        justOver = 2 ^ (64 * 8 :: Integer)
        t1 :: Term
        t1 = UPLC.Delay () $ UPLC.mkConstant () justOver
    assertBool "delayed" (isLeft $ Flat.unflatWith limitedDecoder (Flat.flat t1))
