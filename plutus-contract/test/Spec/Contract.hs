{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Spec.Contract(tests) where

import           Control.Lens                          ((&), (.~))
import           Control.Monad                         (void)
import           Control.Monad.Error.Lens
import           Test.Tasty

import           Language.Plutus.Contract              as Con
import           Language.Plutus.Contract.Tx           as Tx
import           Language.Plutus.Contract.Test
import           Language.Plutus.Contract.Util         (loopM)
import           Language.PlutusTx.Lattice
import qualified Language.PlutusTx                     as PlutusTx
import           Ledger                                (Address)
import qualified Ledger                                as Ledger
import qualified Ledger.Ada                            as Ada
import           Prelude                               hiding (not)
import qualified Wallet.Emulator                       as EM

import qualified Language.Plutus.Contract.Effects.AwaitSlot as AwaitSlot

tests :: TestTree
tests =
    let cp = checkPredicate @Schema @ContractError in
    testGroup "contracts"
        [ cp "awaitSlot"
            (void $ awaitSlot 10)
            (waitingForSlot w1 10)
            $ pure ()

        , cp "selectEither"
            (void $ selectEither (awaitSlot 10) (awaitSlot 5))
            (waitingForSlot w1 5)
            $ pure ()

        , cp "until"
            (void $ awaitSlot 10 `Con.until` 5)
            (waitingForSlot w1 5)
            $ pure ()

        , cp "both"
            (void $ Con.both (awaitSlot 10) (awaitSlot 20))
            (waitingForSlot w1 10)
            $ pure ()

        , cp "both (2)"
            (void $ Con.both (awaitSlot 10) (awaitSlot 20))
            (waitingForSlot w1 20)
            $ addEvent w1 (AwaitSlot.event 10)

        , cp "fundsAtAddressGt"
            (void $ fundsAtAddressGt someAddress (Ada.adaValueOf 10))
            (interestingAddress w1 someAddress)
            $ pure ()

        , cp "watchAddressUntil"
            (void $ watchAddressUntil someAddress 5)
            (interestingAddress w1 someAddress /\ waitingForSlot w1 5)
            $ pure ()

        , cp "endpoint"
            (endpoint @"ep" @())
            (endpointAvailable @"ep" w1)
            $ pure ()

        , cp "call endpoint (1)"
            (void $ endpoint @"1" @Int >> endpoint @"2" @Int)
            (endpointAvailable @"1" w1)
            $ pure ()

        , cp "call endpoint (2)"
            (void $ endpoint @"1" @Int >> endpoint @"2" @Int)
            (endpointAvailable @"2" w1 /\ not (endpointAvailable @"1" w1))
            (callEndpoint @"1" @Int w1 1)

        , cp "call endpoint (3)"
            (void $ endpoint @"1" @Int >> endpoint @"2" @Int)
            (not (endpointAvailable @"2" w1) /\ not (endpointAvailable @"1" w1))
            (callEndpoint @"1" @Int w1 1 >> callEndpoint @"2" @Int w1 1)

        , cp "submit tx"
            (void $ writeTx mempty >> watchAddressUntil someAddress 20)
            (waitingForSlot w1 20 /\ interestingAddress w1 someAddress)
            (handleBlockchainEvents w1 >> addBlocks 1)

        , let smallTx = mempty & Tx.outputs .~ [Tx.pubKeyTxOut (Ada.lovelaceValueOf 10) (walletPubKey (Wallet 2))]
          in cp "handle several blockchain events"
                (writeTx smallTx >> writeTx smallTx)
                (assertDone w1 (const True) "all blockchain events should be processed"
                /\ assertNoFailedTransactions
                /\ walletFundsChange w1 (Ada.lovelaceValueOf (-20)))
                (handleBlockchainEvents w1)

        , cp "select either"
            (let l = endpoint @"1" >> endpoint @"2"
                 r = endpoint @"3" >> endpoint @"4"
                 s :: Contract _ ContractError _
                 s = selectEither l r
            in void s)
            (assertDone w1 (const True) "left branch should finish")
            (callEndpoint @"3" w1 3 >> callEndpoint @"1" w1 1 >> callEndpoint @"2" w1 2)

        , cp "loopM"
            (void $ loopM (\_ -> Left <$> endpoint @"1" @Int) 0)
            (endpointAvailable @"1" w1)
            (callEndpoint @"1" @Int w1 1)

        , cp "collect until"
            (void $ collectUntil (+) 0 (endpoint @"1") 10)
            (endpointAvailable @"1" w1 /\ waitingForSlot w1 10)
            (callEndpoint @"1" @Int w1 1)

        , cp "throw an error"
            (void $ throwing _ContractError $ OtherError "error")
            (assertContractError w1 (OtherError "error") "failed to throw error")
            (pure ())
        ]

w1 :: EM.Wallet
w1 = EM.Wallet 1

someAddress :: Address
someAddress = Ledger.scriptAddress $
    Ledger.mkValidatorScript $$(PlutusTx.compile [|| \(_ :: PlutusTx.Data) (_ :: PlutusTx.Data) (_ :: PlutusTx.Data) -> () ||])

type Schema =
    BlockchainActions
        .\/ Endpoint "1" Int
        .\/ Endpoint "2" Int
        .\/ Endpoint "3" Int
        .\/ Endpoint "4" Int
        .\/ Endpoint "ep" ()
