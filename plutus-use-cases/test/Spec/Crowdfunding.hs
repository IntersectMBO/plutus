{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind #-}
module Spec.Crowdfunding(tests) where

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

import           Language.Plutus.Coordination.Contracts.CrowdFunding (Campaign (..), contribute, refund)
import qualified Language.Plutus.Coordination.Contracts.CrowdFunding as CF
import qualified Language.Plutus.Runtime                             as Runtime
import qualified Wallet.UTXO                                         as UTXO

tests :: TestTree
tests = testGroup "crowdfunding" [
        testProperty "make a contribution" makeContribution,
        testProperty "make contributions and collect" successfulCampaign,
        testProperty "cannot collect money too early" cantCollectEarly,
        testProperty "cannot collect money too late" cantCollectLate,
        testProperty "can claim a refund" canRefund
        ]

-- | Make a contribution to the campaign from a wallet. Returns the reference
--   to the transaction output that is locked by the campaign's validator
--   script (and can be collected by the campaign owner)
contrib :: Wallet -> Campaign -> Runtime.Value -> Trace EmulatedWalletApi  TxOutRef'
contrib w cmp v = exContrib <$> walletAction w (contribute cmp v) where
    exContrib = snd . head . filter (isPayToScriptOut . fst) . txOutRefs . head

-- | Make a contribution from wallet 2
contrib2 :: Campaign -> Runtime.Value -> Trace EmulatedWalletApi  TxOutRef'
contrib2 = contrib (Wallet 2)

-- | Make a contribution from wallet 3
contrib3 :: Campaign -> Runtime.Value -> Trace EmulatedWalletApi  TxOutRef'
contrib3 = contrib (Wallet 3)

-- | Collect the contributions of a crowdfunding campaign
collect :: Wallet -> Campaign -> [(TxOutRef', UTXO.Value)] -> Trace EmulatedWalletApi  [Tx]
collect w c  = walletAction w . CF.collect c

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
    cfWallets = Wallet <$> [1..3]
    cfInitialBalances = Map.fromList [
        (PubKey 1, startingBalance),
        (PubKey 2, startingBalance),
        (PubKey 3, startingBalance)]


-- | Generate a transaction that contributes some funds to a campaign.
--   NOTE: This doesn't actually run the validation script. The script
--         will be run when the funds are retrieved
makeContribution :: Property
makeContribution = checkCFTrace scenario1 $ do
    let w = Wallet 2
        contribution = 600
        rest = startingBalance - fromIntegral contribution
    blockchainActions >>= walletNotifyBlock w
    contrib2 (cfCampaign scenario1) contribution
    blockchainActions >>= walletNotifyBlock w
    assertOwnFundsEq w rest

-- | Run a campaign with two contributions where the campaign owner collects
--   the funds at the end
successfulCampaign :: Property
successfulCampaign = checkCFTrace scenario1 $ do
    let CFScenario c [w1, w2, w3] _ = scenario1
        updateAll' = updateAll scenario1
    updateAll'

    -- wallets 2 and 3 each contribute some funds
    con2 <- contrib2 c 600
    con3 <- contrib3 c 800
    updateAll'

    -- the campaign ends at blockheight 10 (specified in `scenario1`)
    -- so we add a number of empty blocks to ensure that the target
    -- height has ben reached.
    addBlocks 10

    -- Wallet 1 can now collect the contributions. We need the definition
    -- of the campaign, and the UTXOs representing contributions along with
    -- how much money each contribution is worth.
    collect w1 c [(con2, 600), (con3, 800)]
    updateAll'

    -- At the end we verify that the funds owned by wallets 2 and 3 have
    -- decreased by the amount of their contributions. Wallet 1, which started
    -- out with 0 funds, now has the total of all contributions.
    traverse_ (uncurry assertOwnFundsEq) [(w2, startingBalance - 600), (w3, startingBalance - 800), (w1, startingBalance + 600 + 800)]

-- | Check that the campaign owner cannot collect the monies before the campaign deadline
cantCollectEarly :: Property
cantCollectEarly = checkCFTrace scenario1 $ do
    let CFScenario c [w1, w2, w3] _ = scenario1
        updateAll' = updateAll scenario1
    updateAll'
    con2 <- contrib2 c 600
    con3 <- contrib3 c 800
    updateAll'

    -- Unlike in the `successfulCampaign` trace we don't advance the time before
    -- attempting to `collect` the funds. As a result, the transaction
    -- generated by `collect` will fail to validate and the funds remain locked.
    collect w1 c [(con2, 600), (con3, 800)]
    updateAll'
    traverse_ (uncurry assertOwnFundsEq) [(w2, startingBalance - 600), (w3, startingBalance - 800), (w1, startingBalance)]


-- | Check that the campaign owner cannot collect the monies after the
--   collection deadline
cantCollectLate :: Property
cantCollectLate = checkCFTrace scenario1 $ do
    let CFScenario c [w1, w2, w3] _ = scenario1
        updateAll' = updateAll scenario1
    updateAll'
    con2 <- contrib2 c 600
    con3 <- contrib3 c 800
    updateAll'

    -- The deadline for collecting the funds is at 15 blocks (defined in
    -- `scenario1`), so an attempt by the campaign owner to collect the funds
    -- after that should fail.
    addBlocks 15
    collect w1 c [(con2, 600), (con3, 800)]
    updateAll'
    traverse_ (uncurry assertOwnFundsEq) [(w2, startingBalance - 600), (w3, startingBalance - 800), (w1, startingBalance)]

-- | Run a successful campaign that ends with a refund
canRefund :: Property
canRefund = checkCFTrace scenario1 $ do
    let CFScenario c [w1, w2, w3] _ = scenario1
        updateAll' = updateAll scenario1
    updateAll'
    con2 <- contrib2 c 600
    con3 <- contrib3 c 800
    updateAll'

    -- If the funds contributed to the campaign haven't been collected after 15
    -- blocks (as specified in `scenario1`) then the contributors can claim a
    -- refund.
    addBlocks 15
    walletAction w2 (refund c con2 600)
    updateAll'
    walletAction w3 (refund c con3 800)
    updateAll'

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
checkCFTrace :: CFScenario -> Trace EmulatedWalletApi () -> Property
checkCFTrace CFScenario{cfInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = cfInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)

-- | Validate all pending transactions and notify the wallets
updateAll :: CFScenario -> Trace EmulatedWalletApi [Tx]
updateAll CFScenario{cfWallets} =
    blockchainActions >>= walletsNotifyBlock cfWallets
