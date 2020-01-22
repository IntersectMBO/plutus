{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import           Language.Marlowe.Semantics (AccountId (..), Action (..), Case (..), Contract (..), Payee (..),
                                             Token (..), Value (..))
import           Test.Hspec                 (Selector, describe, hspec, it, shouldThrow)
import           Test.Hspec.Marlowe         (assertNoWarnings)
import           Test.HUnit.Lang            (FailureReason (..), HUnitFailure (..))

warningException :: Selector HUnitFailure
warningException (HUnitFailure _ (ExpectedButGot Nothing "Right Nothing" "Right (Just (Slot {getSlot = 5},[TransactionInput {txInterval = (Slot {getSlot = 6},Slot {getSlot = 11}), txInputs = [IDeposit (AccountId 1 (PubKey {getPubKey = 706172747931})) (PubKey {getPubKey = 706172747931}) (Token  ) 100]},TransactionInput {txInterval = (Slot {getSlot = 8},Slot {getSlot = 14}), txInputs = [IDeposit (AccountId 2 (PubKey {getPubKey = 706172747932})) (PubKey {getPubKey = 706172747932}) (Token  ) 300]}],[TransactionPartialPay (AccountId 1 (PubKey {getPubKey = 706172747931})) (Party (PubKey {getPubKey = 706172747932})) (Token  ) 100 500]))")) = True
warningException _ = False

main :: IO ()
main = hspec $ do
    describe "Safe contract" $
        it "should pass the assertion" $ assertNoWarnings Close
    describe "Unsafe contract" $
        it "should fail the assertion" $ (flip shouldThrow warningException) $ assertNoWarnings $ When [
            (Case
               (Deposit
               (AccountId 1 "party1") "party1"
               (Token "" "")
               (Constant 100))
               (When [
               (Case
                   (Deposit
                       (AccountId 2 "party2") "party2"
                       (Token "" "")
                       (Constant 300))
                   (Pay
                       (AccountId 1 "party1")
                       (Party "party2")
                       (Token "" "")
                       (Constant 500)
                       (Pay
                           (AccountId 2 "party2")
                           (Party "party1")
                           (Token "" "")
                           (Constant 300) Close)))] 20 Close))
           ,
           (Case
               (Deposit
               (AccountId 2 "party2") "party2"
               (Token "" "")
               (Constant 300))
               (When [
               (Case
                   (Deposit
                       (AccountId 1 "party1") "party1"
                       (Token "" "")
                       (Constant 500))
                   (Pay
                       (AccountId 1 "party1")
                       (Account
                           (AccountId 2 "party2"))
                       (Token "" "")
                       (Constant 200) Close))] 20 Close))] 15 Close
