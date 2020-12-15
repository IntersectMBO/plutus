{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -w #-}
module Spec.Marlowe.AutoExecute
    ( tests
    )
where

import           Control.Exception                     (SomeException, catch)
import qualified Data.Map.Strict                       as Map
import           Data.Maybe                            (isJust)
import qualified Data.Text                             as T
import qualified Data.Text.IO                          as T
import           Data.Text.Lazy                        (toStrict)
import           Language.Marlowe.Analysis.FSSemantics
import           Language.Marlowe.Client
import           Language.Marlowe.Semantics
import           Language.Marlowe.Util
import           System.IO.Unsafe                      (unsafePerformIO)

import           Data.Aeson                            (decode, encode)
import           Data.Aeson.Text                       (encodeToLazyText)
import qualified Data.ByteString                       as BS
import           Data.Either                           (isRight)
import           Data.Ratio                            ((%))
import           Data.String

import qualified Codec.CBOR.Write                      as Write
import qualified Codec.Serialise                       as Serialise
import           Language.Haskell.Interpreter          (Extension (OverloadedStrings), MonadInterpreter,
                                                        OptionVal ((:=)), as, interpret, languageExtensions,
                                                        runInterpreter, set, setImports)
import           Language.Plutus.Contract.Test
import qualified Language.PlutusTx.AssocMap            as AssocMap
import           Language.PlutusTx.Lattice

import qualified Language.PlutusTx.Prelude             as P
import           Ledger                                hiding (Value)
import qualified Ledger
import           Ledger.Ada                            (lovelaceValueOf)
import           Ledger.Typed.Scripts                  (scriptHash, validatorScript)
import           Spec.Marlowe.Common
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
{-# ANN module ("HLint: ignore Redundant if" :: String) #-}

tests :: TestTree
tests = testGroup "Marlowe Auto Execution"
    [ awaitUntilTimeoutTest
    , autoexecZCBTest
    , autoexecZCBTestAliceWalksAway
    , autoexecZCBTestBobWalksAway
    ]


alice, bob, carol :: Wallet
alice = Wallet 1
bob = Wallet 2
carol = Wallet 3


autoexecZCBTest :: TestTree
autoexecZCBTest = checkPredicate @MarloweSchema @MarloweError "ZCB Auto Execute Contract" marlowePlutusContract
    (assertNoFailedTransactions
    -- /\ emulatorLog (const False) ""
    /\ assertNotDone alice "contract should close"
    /\ assertNotDone bob "contract should close"
    /\ walletFundsChange alice (lovelaceValueOf (150))
    /\ walletFundsChange bob (lovelaceValueOf (-150))
    ) $ do

    -- Bob will wait for the contract to appear on chain
    callEndpoint @"auto" bob (params, bobPk, contractLifespan)
    handleBlockchainEvents bob

    -- Init a contract
    callEndpoint @"create" alice (AssocMap.empty, zeroCouponBond)
    addBlocksNotify 1

    -- Move all Alice's money to Carol, so she can't make a payment
    payToWallet alice carol defaultLovelaceAmount
    addBlocksNotify 1

    callEndpoint @"auto" alice (params, alicePk, contractLifespan)
    handleBlockchainEvents alice -- Here Alice should not be able to pay
    addBlocksNotify 1

    -- Return money to Alice
    payToWallet carol alice defaultLovelaceAmount
    addBlocksNotify 1

    -- Now Alice should be able to retry and pay to Bob
    addBlocksNotify 1
    addBlocksNotify 1


autoexecZCBTestAliceWalksAway :: TestTree
autoexecZCBTestAliceWalksAway = checkPredicate @MarloweSchema @MarloweError
    "ZCB Auto Execute Contract when Alice walks away"
    marlowePlutusContract
    (assertNoFailedTransactions
    -- /\ emulatorLog (const False) ""
    /\ assertNotDone alice "contract should close"
    /\ assertNotDone bob "contract should close"
    /\ walletFundsChange alice (P.inv defaultLovelaceAmount)
    /\ walletFundsChange carol defaultLovelaceAmount
    ) $ do

    -- Bob will wait for the contract to appear on chain
    callEndpoint @"auto" bob (params, bobPk, contractLifespan)
    handleBlockchainEvents bob

    -- Init a contract
    callEndpoint @"create" alice (AssocMap.empty, zeroCouponBond)
    addBlocksNotify 1

    -- Move all Alice's money to Carol, so she can't make a payment
    payToWallet alice carol defaultLovelaceAmount
    addBlocksNotify 1

    callEndpoint @"auto" alice (params, alicePk, contractLifespan)
    handleBlockchainEvents alice -- Here Alice should not be able to pay
    addBlocksNotify 1
    addBlocksNotify 20
    -- Here Alice deposit timeout happened, so Bob should Close the contract
    addBlocksNotify 1


autoexecZCBTestBobWalksAway :: TestTree
autoexecZCBTestBobWalksAway = checkPredicate @MarloweSchema @MarloweError
    "ZCB Auto Execute Contract when Bob walks away"
    marlowePlutusContract
    (assertNoFailedTransactions
    -- /\ emulatorLog (const False) ""
    /\ assertNotDone alice "contract should close"
    /\ assertNotDone bob "contract should close"
    /\ walletFundsChange alice (lovelaceValueOf (-850))
    /\ walletFundsChange carol defaultLovelaceAmount
    ) $ do

    -- Bob will wait for the contract to appear on chain
    callEndpoint @"auto" bob (params, bobPk, contractLifespan)
    handleBlockchainEvents bob

    -- Init a contract
    callEndpoint @"create" alice (AssocMap.empty, zeroCouponBond)
    addBlocksNotify 1

    payToWallet bob carol defaultLovelaceAmount
    addBlocksNotify 1

    callEndpoint @"auto" alice (params, alicePk, contractLifespan)
    handleBlockchainEvents alice
    addBlocksNotify 1 -- Alice pays to Bob
    addBlocksNotify 15 -- Bob can't pay back
    addBlocksNotify 15 -- Bob can't pay back
    addBlocksNotify 15 -- Bob can't pay back, walks away


awaitUntilTimeoutTest :: TestTree
awaitUntilTimeoutTest = checkPredicate @MarloweSchema @MarloweError
    "Party waits for contract to appear on chain until timeout"
    marlowePlutusContract
    (assertNoFailedTransactions
    -- /\ emulatorLog (const False) ""
    /\ assertNotDone bob "contract should close"
    ) $ do

    -- Bob will wait for the contract to appear on chain
    callEndpoint @"auto" bob (params, bobPk, contractLifespan)
    handleBlockchainEvents bob

    addBlocksNotify 15
    addBlocksNotify 15
    -- here Bob gets Timeout and closes the contract
    addBlocksNotify 15


alicePk = PK $ (pubKeyHash $ walletPubKey alice)
bobPk = PK $ (pubKeyHash $ walletPubKey bob)

addBlocksNotify :: Integer -> ContractTrace MarloweSchema MarloweError a ()
addBlocksNotify n = do
    addBlocks n
    handleBlockchainEvents alice
    handleBlockchainEvents bob

params = defaultMarloweParams

zeroCouponBond = When [ Case
        (Deposit alicePk alicePk ada (Constant 850))
        (Pay alicePk (Party bobPk) ada (Constant 850)
            (When
                [ Case (Deposit alicePk bobPk ada (Constant 1000)) Close] 40 Close
            ))] 20 Close

contractLifespan = contractLifespanUpperBound zeroCouponBond

defaultLovelaceAmount :: Ledger.Value
defaultLovelaceAmount = defaultDist Map.! alice
