{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Spec.Crowdfunding(tests) where

import           Data.Bifunctor                                      (Bifunctor (..))
import           Data.Either                                         (isLeft, isRight)
import qualified Data.Map                                            as Map
import           Hedgehog                                            (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen                                        as Gen
import qualified Hedgehog.Range                                      as Range
import           Lens.Micro
import           Test.Tasty
import           Test.Tasty.Hedgehog                                 (testProperty)

import           Wallet.API                                          (PubKey (..))
import           Wallet.Emulator                                     hiding (Value)
import           Wallet.Generators                                   (Mockchain (..))
import qualified Wallet.Generators                                   as Gen

import           Language.Plutus.Coordination.Contracts.CrowdFunding (Campaign (..), CampaignActor, CampaignPLC (..),
                                                                      contribute, refund)
import qualified Language.Plutus.Coordination.Contracts.CrowdFunding as CF
import qualified Language.Plutus.Runtime                             as Runtime
import           Language.Plutus.TH                                  (plutus)
import qualified Wallet.UTXO                                         as UTXO

import           Spec.TH                                             (pendingTxCrowdfunding)

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
contrib :: Wallet -> CampaignPLC -> Runtime.Value -> Trace TxOutRef'
contrib w c v = exContrib <$> walletAction w (contribute c v) where
    exContrib = snd . head . filter (isPayToScriptOut . fst) . txOutRefs . head

-- | Collect the contributions of a crowdfunding campaign
collect :: Wallet -> CampaignPLC -> [(TxOutRef', Wallet, UTXO.Value)] -> Trace [Tx]
collect w c contributions = walletAction w $ CF.collect c ins where
    ins = first (PubKey . getWallet) <$> contributions

-- | Generate a transaction that contributes some funds to a campaign.
--   NOTE: This doesn't actually run the validation script. The script
--         will be run when the funds are retrieved
makeContribution :: Property
makeContribution = checkCFTrace scenario1 $ do
    let w = Wallet 2
        contribution = 600
        rest = fromIntegral $ 1000 - contribution
    blockchainActions >>= walletNotifyBlock w
    contrib w (cfCampaign scenario1) contribution
    blockchainActions >>= walletNotifyBlock w
    assertOwnFundsEq w rest

-- | Run a campaign with two contributions where the campaign owner collects
--   the funds at the end
successfulCampaign :: Property
successfulCampaign = checkCFTrace scenario1 $ do
    let CFScenario c [w1, w2, w3] _ = scenario1
        updateAll' = updateAll scenario1
    updateAll'
    con2 <- contrib w2 c 600
    con3 <- contrib w3 c 800
    updateAll'
    setValidationData $ ValidationData $(plutus [| $(pendingTxCrowdfunding) 11 600 (Just 800) |])
    collect w1 c [(con2, w2, 600), (con3, w3, 800)]
    updateAll'
    mapM_ (uncurry assertOwnFundsEq) [(w2, 400), (w3, 200), (w1, 1400)]

-- | Check that the campaign owner cannot collect the monies before the campaign deadline
cantCollectEarly :: Property
cantCollectEarly = checkCFTrace scenario1 $ do
    let CFScenario c [w1, w2, w3] _ = scenario1
        updateAll' = updateAll scenario1
    updateAll'
    con2 <- contrib w2 c 600
    con3 <- contrib w3 c 800
    updateAll'
    setValidationData $ ValidationData $(plutus [| $(pendingTxCrowdfunding) 8 600 (Just 800) |])
    collect w1 c [(con2, w2, 600), (con3, w3, 800)]
    updateAll'
    mapM_ (uncurry assertOwnFundsEq) [(w2, 400), (w3, 200), (w1, 0)]


-- | Check that the campaign owner cannot collect the monies after the
--   collection deadline
cantCollectLate :: Property
cantCollectLate = checkCFTrace scenario1 $ do
    let CFScenario c [w1, w2, w3] _ = scenario1
        updateAll' = updateAll scenario1
    updateAll'
    con2 <- contrib w2 c 600
    con3 <- contrib w3 c 800
    updateAll'
    setValidationData $ ValidationData $(plutus [| $(pendingTxCrowdfunding) 17 600 (Just 800) |])
    collect w1 c [(con2, w2, 600), (con3, w3, 800)]
    updateAll'
    mapM_ (uncurry assertOwnFundsEq) [(w2, 400), (w3, 200), (w1, 0)]


-- | Run a successful campaign that ends with a refund
canRefund :: Property
canRefund = checkCFTrace scenario1 $ do
    let CFScenario c [w1, w2, w3] _ = scenario1
        updateAll' = updateAll scenario1
    updateAll'
    con2 <- contrib w2 c 600
    con3 <- contrib w3 c 800
    updateAll'
    setValidationData $ ValidationData $(plutus [| $(pendingTxCrowdfunding) 18 600 Nothing |])
    walletAction w2 (refund c con2 600)
    walletAction w3 (refund c con3 800)
    updateAll'
    mapM_ (uncurry assertOwnFundsEq) [(w2, 1000), (w3, 1000), (w1, 0)]

-- | Crowdfunding scenario with test parameters
data CFScenario = CFScenario {
    cfCampaign        :: CampaignPLC,
    cfWallets         :: [Wallet],
    cfInitialBalances :: Map.Map PubKey UTXO.Value
    }

scenario1 :: CFScenario
scenario1 = CFScenario{..} where
    cfCampaign = CampaignPLC $(plutus [| Campaign {
        campaignDeadline = 10,
        campaignTarget   = 1000,
        campaignCollectionDeadline = 15,
        campaignOwner              = PubKey 1
        } |])
    cfWallets = Wallet <$> [1..3]
    cfInitialBalances = Map.fromList [
        (PubKey 1, 0),
        (PubKey 2, 1000),
        (PubKey 3, 1000)]

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkCFTrace :: CFScenario -> Trace () -> Property
checkCFTrace CFScenario{cfInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = cfInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)

-- | Validate all pending transactions and notify the wallets
updateAll :: CFScenario -> Trace [Tx]
updateAll CFScenario{cfWallets} =
    blockchainActions >>= walletsNotifyBlock cfWallets
