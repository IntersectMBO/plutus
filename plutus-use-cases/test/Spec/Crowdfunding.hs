{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind #-}
module Spec.Crowdfunding(tests) where

import           Control.Monad.Except
import           Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BSL
import           Data.Foldable                                         (traverse_)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Spec.Lib                                              as Lib
import           Spec.Lib                                              (timesFeeAdjust)
import           Test.Tasty
import qualified Test.Tasty.HUnit                                      as HUnit
import           Test.Tasty.Golden                                     (goldenVsString)

import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Effects.AwaitSlot as AwaitSlot
import           Language.Plutus.Contract.Test
import qualified Language.Plutus.Contract.Trace                        as Trace
import qualified Language.PlutusTx                                     as PlutusTx
import qualified Language.PlutusTx.Prelude                             as PlutusTx
import           Language.PlutusTx.Lattice
import           Language.PlutusTx.Coordination.Contracts.CrowdFunding
import qualified Ledger.Ada                                            as Ada

w1, w2, w3, w4 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3
w4 = Wallet 4

theContract :: Contract CrowdfundingSchema T.Text ()
theContract = crowdfunding theCampaign

tests :: TestTree
tests = testGroup "crowdfunding"
    [ checkPredicate "Expose 'contribute' and 'scheduleCollection' endpoints"
        theContract
        (endpointAvailable @"contribute" w1 /\ endpointAvailable @"schedule collection" w1)
        $ pure ()

    , checkPredicate "make contribution"
        theContract
        (walletFundsChange w1 (1 `timesFeeAdjust` (-10)))
        $ let contribution = Ada.lovelaceValueOf 10
          in makeContribution w1 contribution

    , checkPredicate "make contributions and collect"
        theContract
        (walletFundsChange w1 (1 `timesFeeAdjust` 21))
        $ successfulCampaign

    , checkPredicate "cannot collect money too early"
        theContract
        (walletFundsChange w1 PlutusTx.zero
        /\ assertNoFailedTransactions)
        $ startCampaign
            >> makeContribution w2 (Ada.lovelaceValueOf 10)
            >> makeContribution w3 (Ada.lovelaceValueOf 10)
            >> makeContribution w4 (Ada.lovelaceValueOf 1)
            -- Tell the contract we're at slot 21, causing the transaction to be submitted
            >> Trace.addEvent w1 (AwaitSlot.event 21)
            -- This submits the transaction to the blockchain. Normally, the transaction would
            -- be validated right away and the funds of wallet 1 would increase. In this case
            -- the transaction is not validated because it has a validity interval that begins
            -- _after_ the campaign deadline.
            >> Trace.handleBlockchainEvents w1

    , checkPredicate "cannot collect money too late"
        theContract
        (walletFundsChange w1 PlutusTx.zero
        /\ assertNoFailedTransactions)
        $ startCampaign
            >> makeContribution w2 (Ada.lovelaceValueOf 10)
            >> makeContribution w3 (Ada.lovelaceValueOf 10)
            >> makeContribution w4 (Ada.lovelaceValueOf 1)
            -- Add some blocks to bring the total up to 31
            -- (that is, above the collection deadline)
            >> Trace.addBlocks 26
            -- Then inform the wallet. It's too late to collect the funds
            -- now.
            >> Trace.notifySlot w1
            >> Trace.handleBlockchainEvents w1
            >> Trace.addBlocks 1

    , checkPredicate "cannot collect unless notified"
        theContract
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
        theContract
        (walletFundsChange w2 (2 `timesFeeAdjust` 0)
            /\ walletFundsChange w3 (2 `timesFeeAdjust` 0))
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

    , goldenVsString
        "renders the context of a trace sensibly"
        "test/Spec/crowdfundingTestOutput.txt"
        (renderPredicate 
            (crowdfunding theCampaign) 
            successfulCampaign)

    , goldenVsString
        "renders an error sensibly"
        "test/Spec/contractError.txt"
        (renderPredicate
            (throwError "something went wrong")
            (startCampaign))
    ]

renderPredicate 
    :: Contract CrowdfundingSchema T.Text ()
    -> ContractTrace CrowdfundingSchema T.Text (EmulatorAction T.Text) () ()
    -> IO ByteString
renderPredicate contract trace = do
    case runTrace contract trace of
        (Left err, _) ->
            HUnit.assertFailure $ "EmulatorAction failed. " ++ show err
        (Right (_, st), _) -> do
            pure $ BSL.fromStrict $ T.encodeUtf8 $ renderTraceContext mempty st
            
