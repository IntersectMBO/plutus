module Spec.Crowdfunding(tests) where

import           Test.Tasty

import qualified Ledger.Ada            as Ada
import qualified Wallet.Emulator       as EM

import           Examples.Crowdfunding

import           Spec.HUnit

tests :: TestTree
tests = testGroup "crowdfunding" [
    checkPredicate "Expose 'contribute' and 'scheduleCollection' endpoints"
        crowdfunding
        (endpointAvailable w1 "contribute" <> endpointAvailable w1 "schedule collection")
        $ pure ()

    , checkPredicate "'contribute' endpoint submits a transaction"
        crowdfunding
        (interestingAddress w1 (campaignAddress theCampaign) <> walletFundsChange w1 (Ada.adaValueOf (-10)))
        $ let key = EM.walletPubKey w1
              contribution = Ada.adaValueOf 10
          in callEndpoint w1 "contribute" (key, contribution)
                >> handleBlockchainEvents w1
                >> notifyInterestingAddresses w1

    , checkPredicate "'scheduleCollection' starts watching campaign address and waits for deadline"
        crowdfunding
        (waitingForSlot w1 (campaignDeadline theCampaign) <> interestingAddress w1 (campaignAddress theCampaign))
        $ callEndpoint w1 "schedule collection" ()
    ]

w1 :: EM.Wallet
w1 = EM.Wallet 1
