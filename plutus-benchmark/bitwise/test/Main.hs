{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Crypto.Hash.SHA512 qualified as SHA512Ref
import Crypto.Sign.Ed25519 (PublicKey (PublicKey), Signature (Signature))
import Crypto.Sign.Ed25519 qualified as Ed25519Ref
import PlutusBenchmark.Ed25519 (checkValid)
import PlutusBenchmark.SHA512 (sha512)
import PlutusTx.Builtins (fromBuiltin, toBuiltin)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

main :: IO ()
main = defaultMain . testGroup "nqueens" $ [
  testCase "solves for 8 queens" $ assertEqual ""
    [(0,0), (1,4), (2,7), (3,5), (4,2), (5,6), (6,1), (7,3)]
    (nqueens 8),
  testGroup "Ed25519" [
    testCase "SHA512 works" sha512Case,
    testCase "Ed25519 works" ed25519Case
    ]
  ]

-- Cases

sha512Case :: IO ()
sha512Case = do
  let testBS = "hello world"
  let expected = SHA512Ref.hash testBS
  let actual = fromBuiltin . sha512 . toBuiltin $ testBS
  assertEqual "" expected actual

ed25519Case :: IO ()
ed25519Case = do
  let msg = "hello world"
  (refPK@(PublicKey pk), refSK) <- Ed25519Ref.createKeypair
  let signed@(Signature sigRaw) = Ed25519Ref.dsign refSK msg
  let expected = Ed25519Ref.dverify refPK msg signed
  let actual = checkValid (toBuiltin sigRaw) (toBuiltin msg) (toBuiltin pk)
  assertEqual "" expected actual
