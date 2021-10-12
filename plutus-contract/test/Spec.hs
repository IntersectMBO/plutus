{-# LANGUAGE OverloadedStrings #-}
module Main(main) where

import qualified Spec.Contract
import qualified Spec.Emulator
import qualified Spec.ErrorChecking
import qualified Spec.Rows
import qualified Spec.Secrets
import qualified Spec.State
import qualified Spec.ThreadToken
import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutus-contract" [
    Spec.Contract.tests,
    Spec.Emulator.tests,
    Spec.State.tests,
    Spec.Rows.tests,
    Spec.ThreadToken.tests,
    Spec.Secrets.tests,
    Spec.ErrorChecking.tests
    ]
