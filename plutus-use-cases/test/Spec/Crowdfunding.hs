{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind #-}
module Spec.Crowdfunding(tests) where

import           Data.Foldable                                         (traverse_)
import qualified Spec.Lib                                              as Lib
import           Spec.Lib                                              (timesFeeAdjust)
import           Test.Tasty
import qualified Test.Tasty.HUnit                                      as HUnit

import qualified Language.Plutus.Contract.Prompt.Event                 as Event
import           Language.Plutus.Contract.Test
import qualified Language.Plutus.Contract.Trace                        as Trace
import qualified Language.PlutusTx                                     as PlutusTx
import qualified Language.PlutusTx.Prelude                             as PlutusTx
import           Language.PlutusTx.Coordination.Contracts.CrowdFunding
import qualified Ledger.Ada                                            as Ada

w1, w2, w3, w4 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3
w4 = Wallet 4

tests :: TestTree
tests = testGroup "crowdfunding"
    [ checkPredicate "Expose 'contribute' and 'scheduleCollection' endpoints"
        (crowdfunding theCampaign)
        (endpointAvailable w1 "contribute" <> endpointAvailable w1 "schedule collection")
        $ pure ()

    , checkPredicate "make contribution"
        (crowdfunding theCampaign)
        (walletFundsChange w1 (1 `timesFeeAdjust` (-10)))
        $ let contribution = Ada.lovelaceValueOf 10
          in makeContribution w1 contribution

    , checkPredicate "make contributions and collect"
        (crowdfunding theCampaign)
        (walletFundsChange w1 (1 `timesFeeAdjust` 21))
        $ successfulCampaign

    , checkPredicate "cannot collect money too early"
        (crowdfunding theCampaign)
        (walletFundsChange w1 PlutusTx.zero)
        $ startCampaign
            >> makeContribution w2 (Ada.lovelaceValueOf 10)
            >> makeContribution w3 (Ada.lovelaceValueOf 10)
            >> makeContribution w4 (Ada.lovelaceValueOf 1)
            -- Tell the contract we're at slot 21, causing the transaction to be submitted
            >> Trace.addEvent w1 (Event.changeSlot 21)
            -- This submits the transaction to the blockchain. Normally, the transaction would
            -- be validated right away and the funds of wallet 1 would increase. In this case
            -- the transaction is not validated because it has a validity interval that begins
            -- _after_ the campaign deadline.
            >> Trace.handleBlockchainEvents w1

    , checkPredicate "cannot collect money too late"
        (crowdfunding theCampaign)
        (walletFundsChange w1 PlutusTx.zero)
        $ startCampaign
            >> makeContribution w2 (Ada.lovelaceValueOf 10)
            >> makeContribution w3 (Ada.lovelaceValueOf 10)
            >> makeContribution w4 (Ada.lovelaceValueOf 1)
            -- Add some blocks to bring the total up to 31
            -- (that is, above the collection deadline)
            >> Trace.addBlocks 25
            -- Then inform the wallet. It's too late to collect the funds
            -- now.
            >> Trace.notifySlot w1
            >> Trace.handleBlockchainEvents w1

    , checkPredicate "cannot collect unless notified"
        (crowdfunding theCampaign)
        (walletFundsChange w1 PlutusTx.zero)
        $ startCampaign
            >> makeContribution w2 (Ada.lovelaceValueOf 10)
            >> makeContribution w3 (Ada.lovelaceValueOf 10)
            >> makeContribution w4 (Ada.lovelaceValueOf 1)
            >> Trace.addBlocks 18
            -- The contributions could be collected now, but without the
            -- call to 'Trace.notifySlot' wallet 1 is not aware that the
            -- time has come, so it does not submit the transaction.
            >> Trace.handleBlockchainEvents w1

    , checkPredicate "can claim a refund"
        (crowdfunding theCampaign)
        (walletFundsChange w2 (2 `timesFeeAdjust` 0)
            <> walletFundsChange w3 (2 `timesFeeAdjust` 0))
        $ startCampaign
            >> makeContribution w2 (Ada.lovelaceValueOf 5)
            >> makeContribution w3 (Ada.lovelaceValueOf 5)
            >> Trace.addBlocks 25
            >> Trace.notifySlot w2
            >> Trace.notifySlot w3
            >> traverse_ Trace.handleBlockchainEvents Trace.allWallets

    , Lib.goldenPir "test/Spec/crowdfunding.pir" $$(PlutusTx.compile [|| mkValidator ||])
    ,   let
            deadline = 10
            target = Ada.lovelaceValueOf 1000
            collectionDeadline = 15
            owner = w1
            cmp = mkCampaign deadline target collectionDeadline owner
        in HUnit.testCase "script size is reasonable" (Lib.reasonable (contributionScript cmp) 50000)
    ]
