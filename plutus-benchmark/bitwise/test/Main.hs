-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Crypto.Hash.SHA512 qualified as SHA512Ref
import Crypto.Sign.Ed25519 (PublicKey (PublicKey), Signature (Signature))
import Crypto.Sign.Ed25519 qualified as Ed25519Ref
import PlutusBenchmark.Ed25519 (checkValid)
import PlutusBenchmark.Ed25519.Compiled (checkValidCompiled, msgAsData, pkAsData, signatureAsData)
import PlutusBenchmark.NQueens (nqueens)
import PlutusBenchmark.NQueens.Compiled (dimAsData, nqueensCompiled)
import PlutusBenchmark.SHA512 (sha512)
import PlutusTx.Builtins (fromBuiltin, toBuiltin)
import PlutusTx.Code (unsafeApplyCode)
import PlutusTx.Test (goldenBundle')
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Extras (TestNested, runTestNested, testNestedGhc)
import Test.Tasty.HUnit (assertEqual, testCase)

main :: IO ()
main =
  defaultMain . testGroup "bitwise" $
    [ testGroup
        "N-queens"
        [ testCase "solves for 8 queens" $
            assertEqual
              ""
              [(0, 0), (1, 4), (2, 7), (3, 5), (4, 2), (5, 6), (6, 1), (7, 3)]
              (nqueens 8)
        , runTestGhc
            [goldenBundle' "8 queens" $ nqueensCompiled `unsafeApplyCode` dimAsData]
        ]
    , testGroup
        "Ed25519"
        [ testCase "SHA512 works" sha512Case
        , testCase "Ed25519 works" ed25519Case
        , runTestGhc
            [ goldenBundle' "Ed25519" $
                checkValidCompiled `unsafeApplyCode` signatureAsData `unsafeApplyCode` msgAsData `unsafeApplyCode` pkAsData
            ]
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
  let signature = "\NUL\147!x\173\167\209z`\t\243|\195$X$\233\166\234\NUL\134\152l\DC4\243\&4\217\NAK\152\180{$M\227R\214\218%\241\157\ENQ\SO\ENQ\t\152\140\171\240\200f\184\133\203\227z\163\NUL\185\155Y\139\178\249\STX"
  let pk = "(:\255\251\129\&7-^w\253\145\vh\ESC\171r\189\223/\213Qzb\249\175$z\211q\195\DC1\198"
  let expected = Ed25519Ref.dverify (PublicKey pk) msg (Signature signature)
  let actual = checkValid (toBuiltin signature) (toBuiltin msg) (toBuiltin pk)
  assertEqual "" expected actual

-- Helpers

runTestGhc :: [TestNested] -> TestTree
runTestGhc = runTestNested ["bitwise", "test"] . pure . testNestedGhc
