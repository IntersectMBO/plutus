{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import VotingContract
import Ledger
import Plutus.Trace.Emulator as Emulator
import Wallet.Emulator.Wallet

main :: IO ()
main = runEmulatorTraceIO $ do
    let datum = VoteDatum ["A","B"] [("A",0),("B",0)]
        redeemer = "A"
    h1 <- activateContractWallet (Wallet 1) typedVotingValidator
    callEndpoint @"vote" h1 (datum, redeemer)
    void $ Emulator.waitNSlots 1
