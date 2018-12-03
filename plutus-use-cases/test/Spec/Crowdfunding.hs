{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind #-}
module Spec.Crowdfunding(tests) where

import           Control.Monad                                       (void)
import           Data.Either                                         (isRight)
import           Data.Foldable                                       (traverse_)
import qualified Data.Map                                            as Map
import           Hedgehog                                            (Property, forAll, property)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog                                 (testProperty)

import           Wallet.API                                          (PubKey (..))
import           Wallet.Emulator                                     hiding (Value)
import qualified Wallet.Generators                                   as Gen

import           Language.Plutus.Coordination.Contracts.CrowdFunding (Campaign (..), contribute)
import qualified Language.Plutus.Coordination.Contracts.CrowdFunding as CF
import qualified Language.Plutus.Runtime                             as Runtime
import qualified Wallet.UTXO                                         as UTXO

tests :: TestTree
tests = testGroup "crowdfunding" [
        testProperty "make a contribution" makeContribution,
        testProperty "make contributions and collect" successfulCampaign,
        testProperty "cannot collect money too early" cantCollectEarly,
        testProperty "cannot collect money too late" cantCollectLate,
        testProperty "cannot collect unless notified" cantCollectUnlessNotified,
        testProperty "can claim a refund" canRefund
        ]

-- | Make a contribution to the campaign from a wallet. Returns the reference
--   to the transaction output that is locked by the campaign's validator
--   script (and can be collected by the campaign owner)
contrib :: Wallet -> Runtime.Value -> Trace MockWallet ()
contrib w v = void $ walletAction w (contribute cmp v) where
    cmp = cfCampaign scenario1

-- | Make a contribution from wallet 2
contrib2 :: Runtime.Value -> Trace MockWallet ()
contrib2 = contrib (Wallet 2)

-- | Make a contribution from wallet 3
contrib3 :: Runtime.Value -> Trace MockWallet ()
contrib3 = contrib (Wallet 3)

-- | Collect the contributions of a crowdfunding campaign
collect :: Wallet -> Trace MockWallet ()
collect w = void $ walletAction w $ CF.collect $ cfCampaign scenario1

-- | The scenario used in the property tests. In includes a campaign
--   definition and the initial distribution of funds to the wallets
--   that are involved in the campaign.
scenario1 :: CFScenario
scenario1 = CFScenario{..} where
    cfCampaign = Campaign {
        campaignDeadline = Runtime.Height 10,
        campaignTarget   = 1000,
        campaignCollectionDeadline = Runtime.Height 15,
        campaignOwner              = PubKey 1
        }
    cfWallets = [w1, w2, w3]
    cfInitialBalances = Map.fromList [
        (PubKey 1, startingBalance),
        (PubKey 2, startingBalance),
        (PubKey 3, startingBalance)]

w1, w2, w3 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3

-- | Generate a transaction that contributes 600 ada to a campaign.
--   NOTE: This doesn't actually run the validation script. The script
--         will be run when the funds are retrieved
makeContribution :: Property
makeContribution = checkCFTrace scenario1 $ do
    let w = Wallet 2
        rest = startingBalance - 600
    contrib2 600
    processPending >>= notifyBlock
    assertOwnFundsEq w rest

-- | Run a campaign with two contributions where the campaign owner collects
--   the funds at the end
successfulCampaign :: Property
successfulCampaign = checkCFTrace scenario1 $ do
    collect w1

    -- wallets 2 and 3 each contribute some funds
    contrib2 600 >> contrib3 800
    processPending >>= notifyBlock

    -- the campaign ends at blockheight 10 (specified in `scenario1`)
    -- so we add a number of empty blocks to ensure that the target
    -- height has ben reached.
    blcks <- addBlocks 10

    -- Once we have notified the wallets of the new blocks, wallet 1 will submit
    -- the "collect funds" transaction, consuming the two contributions
    notifyBlocks blcks
    processPending >>= notifyBlock

    -- At the end we verify that the funds owned by wallets 2 and 3 have
    -- decreased by the amount of their contributions. Wallet 1, which started
    -- out with 0 funds, now has the total of all contributions.
    traverse_ (uncurry assertOwnFundsEq) [(w2, startingBalance - 600), (w3, startingBalance - 800), (w1, startingBalance + 600 + 800)]

-- | Check that the campaign owner cannot collect the monies before the campaign deadline
cantCollectEarly :: Property
cantCollectEarly = checkCFTrace scenario1 $ do
    contrib2 600 >> contrib3 800
    processPending >>= notifyBlock

    -- Unlike in the `successfulCampaign` trace we don't advance the time before
    -- attempting to `collect` the funds. As a result, the transaction
    -- generated by `collect` will fail to validate and the funds remain locked.
    collect w1
    processPending >>= notifyBlock

    traverse_ (uncurry assertOwnFundsEq) [(w2, startingBalance - 600), (w3, startingBalance - 800), (w1, startingBalance)]

-- | Check that a campaign results in a refund if the `collect` trigger is
--   registered too late (that is, after the contributions have already been
--   made)
cantCollectUnlessNotified :: Property
cantCollectUnlessNotified = checkCFTrace scenario1 $ do
    contrib2 600
    processPending >>= notifyBlock

    -- By performing `collect w1` only now, after `contrib2 600` is through,
    -- `w1` misses the first contribution and so never knows that enough funds
    -- have been sent to the campaign address
    collect w1
    processPending >>= notifyBlock

    -- `contrib3 800` is the only contribution that `w1` sees
    contrib3 800
    processPending >>= notifyBlock

    addBlocks 10 >>= notifyBlocks

    -- At this point there are enough funds at the campaign address,
    -- and the block height is in the desired range. However, w1 is not aware
    -- of the first contribution, so its `collectFunds` trigger never fires and
    -- the funds remain locked. (They can be claimed back by w2 and w3 later,
    -- as demonstrated in `canRefund`)
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, startingBalance),
        (w2, startingBalance - 600),
        (w3, startingBalance - 800)]


-- | Check that the campaign owner cannot collect the monies after the
--   collection deadline
cantCollectLate :: Property
cantCollectLate = checkCFTrace scenario1 $ do
    contrib2 600 >> contrib3 800
    processPending >>= notifyBlock
    collect w1

    -- The deadline for collecting the funds is at 15 blocks (defined in
    -- `scenario1`). With `addBlocks 15` we add 15 new blocks *before* notifying
    -- the wallets of them. The trigger for `collectFunds` is still going to
    -- fire, but the transaction will be rejected (because when that
    -- transaction is validated, the blockchain is already too long, so the
    -- validation script fails).
    addBlocks 15 >>= notifyBlocks
    processPending >>= notifyBlock

    traverse_ (uncurry assertOwnFundsEq) [(w2, startingBalance), (w3, startingBalance), (w1, startingBalance)]

-- | Run a successful campaign that ends with a refund
canRefund :: Property
canRefund = checkCFTrace scenario1 $ do
    contrib2 600 >> contrib3 800
    processPending >>= notifyBlock

    -- If the funds contributed to the campaign haven't been collected after 15
    -- blocks (as specified in `scenario1`) then the contributors can claim a
    -- refund.
    addBlocks 15 >>= notifyBlocks
    processPending >>= notifyBlock

    -- Now all wallets are back to their starting balances.
    -- NB On the real blockchain they would have slightly less than their
    -- starting balances because of transaction fees. In the mockchain we
    -- currently set all fees to 0.
    traverse_ (uncurry assertOwnFundsEq) [
        (w2, startingBalance),
        (w3, startingBalance),
        (w1, startingBalance)]

-- | Crowdfunding scenario with test parameters
data CFScenario = CFScenario {
    cfCampaign        :: Campaign,
    cfWallets         :: [Wallet],
    cfInitialBalances :: Map.Map PubKey UTXO.Value
    }

-- | Funds available to wallets `Wallet 2` and `Wallet 3`
startingBalance :: UTXO.Value
startingBalance = 1000

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkCFTrace :: CFScenario -> Trace MockWallet () -> Property
checkCFTrace CFScenario{cfInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = cfInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model (processPending >>= notifyBlock >> t)
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)

-- | Notify all wallets in the campaign of the new blocks.
notifyBlocks :: [Block] -> Trace MockWallet ()
notifyBlocks = traverse_ notifyBlock

-- | Notify all wallets in the campaign of a new block
notifyBlock :: Block -> Trace MockWallet ()
notifyBlock = void . walletsNotifyBlock [w1, w2, w3]
