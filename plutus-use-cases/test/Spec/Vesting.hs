{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Spec.Vesting(tests) where

import           Control.Monad                                  (void)
import           Data.Either                                    (isRight)
import qualified Data.Map                                       as Map
import           Hedgehog                                       (Property, forAll, property)
import qualified Hedgehog
import qualified Hedgehog.Gen                                   as Gen
import           Test.Tasty
import           Test.Tasty.Hedgehog                            (testProperty)

import           Language.Plutus.Coordination.Contracts.Vesting (Vesting (..), VestingData (..), VestingPLC (..),
                                                                 VestingTranche (..), retrieveFunds, vestFunds)
import           Language.Plutus.Runtime                        (Hash (..), PendingTx (..), PendingTxIn (..),
                                                                 PendingTxOut (..), PendingTxOutRef (..),
                                                                 PendingTxOutType (..), Value)
import           Language.Plutus.TH                             (plutus)
import           Wallet.API                                     (PubKey (..))
import           Wallet.Emulator                                hiding (Value)
import qualified Wallet.Generators                              as Gen
import qualified Wallet.UTXO                                    as UTXO

tests :: TestTree
tests = testGroup "vesting" [
    testProperty "secure some funds with the vesting script" secureFunds,
    testProperty "retrieve some funds" canRetrieveFunds,
    testProperty "cannot retrieve more than allowed" cannotRetrieveTooMuch
    ]

-- | Commit some funds from a wallet to a vesting scheme. Returns the reference
--   to the transaction output that is locked by the schemes's validator
--   script (and can be collected by the scheme's owner)
commit :: Wallet -> Vesting -> VestingPLC -> Value -> Trace TxOutRef'
commit w vv vplc vl = exScriptOut <$> walletAction w (void $ vestFunds vplc vv vl) where
    exScriptOut = snd . head . filter (isPayToScriptOut . fst) . txOutRefs . head

secureFunds :: Property
secureFunds = checkVestingTrace scen1 $ do
    let VestingScenario splc s [w1, w2] _ = scen1
        total = 600
        updateAll' = updateAll scen1
    updateAll'
    _ <- commit w2 s splc total
    updateAll'
    mapM_ (uncurry assertOwnFundsEq) [(w2, 400), (w1, 1000)]

canRetrieveFunds :: Property
canRetrieveFunds = checkVestingTrace scen1 $ do
    let VestingScenario splc s [w1, w2] _ = scen1
        total = 600
        updateAll' = updateAll scen1
    updateAll'
    ref <- commit w2 s splc total
    updateAll'
    setValidationData $ ValidationData $(plutus [| PendingTx {
        pendingTxCurrentInput = (PendingTxIn (PendingTxOutRef 100 0) (), 600),
        pendingTxOtherInputs  = []::[(PendingTxIn (), Value)],
        pendingTxOutputs      = (PendingTxOut 150 Nothing (PubKeyTxOut (PubKey 1))::(PendingTxOut VestingData)):(PendingTxOut 450 (Just (VestingData 1123 150)) DataTxOut::(PendingTxOut VestingData)):([]::[PendingTxOut VestingData]),
        pendingTxForge        = 0,
        pendingTxFee          = 0,
        pendingTxBlockHeight  = 11
        } |])
    let ds = DataScript $(plutus [|  VestingData 1123 150 |])
    walletAction w1 $ void (retrieveFunds s splc (VestingData 1123 0) ds ref 150)
    updateAll'
    mapM_ (uncurry assertOwnFundsEq) [(w2, 400), (w1, 1150)]

cannotRetrieveTooMuch :: Property
cannotRetrieveTooMuch = checkVestingTrace scen1 $ do
    let VestingScenario splc s [w1, w2] _ = scen1
        total = 600
        updateAll' = updateAll scen1
    updateAll'
    ref <- commit w2 s splc total
    updateAll'
    setValidationData $ ValidationData $(plutus [|

        let tooMuch = 250 in -- at block height 11, not more than 200 may be taken out
        PendingTx {
            pendingTxCurrentInput = (PendingTxIn (PendingTxOutRef 100 0) (), 600),
            pendingTxOtherInputs  = []::[(PendingTxIn (), Value)],
            pendingTxOutputs      = (PendingTxOut tooMuch Nothing (PubKeyTxOut (PubKey 1))::(PendingTxOut VestingData)):(PendingTxOut 350 (Just (VestingData 1123 250)) DataTxOut::(PendingTxOut VestingData)):([]::[PendingTxOut VestingData]),
            pendingTxForge        = 0,
            pendingTxFee          = 0,
            pendingTxBlockHeight  = 11
        } |])
    let ds = DataScript $(plutus [|  VestingData 1123 150 |])
    walletAction w1 $ void (retrieveFunds s splc (VestingData 1123 0) ds ref 300)
    updateAll'
    mapM_ (uncurry assertOwnFundsEq) [(w2, 400), (w1, 1000)]

-- | Vesting scenario with test parameters
data VestingScenario = VestingScenario {
    vsVestingSchemePLC :: VestingPLC,
    vsVestingScheme    :: Vesting,
    vsWallets          :: [Wallet],
    vsInitialBalances  :: Map.Map PubKey UTXO.Value
    }

scen1 :: VestingScenario
scen1 = VestingScenario{..} where
    vsVestingSchemePLC = VestingPLC $(plutus [|  Vesting {
        vestingTranche1 = VestingTranche 10 200,
        vestingTranche2 = VestingTranche 20 400,
        vestingOwner    = PubKey 1 } |])
    -- Duplication is necessary here until we can translate `vsVestingScheme` to PLC automatically (see [CGP-228])
    vsVestingScheme = Vesting {
        vestingTranche1 = VestingTranche 10 200,
        vestingTranche2 = VestingTranche 20 400,
        vestingOwner    = PubKey 1 }
    vsWallets = Wallet <$> [1..2]
    vsInitialBalances = Map.fromList [
        (PubKey 1, 1000),
        (PubKey 2, 1000)]

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkVestingTrace :: VestingScenario -> Trace () -> Property
checkVestingTrace VestingScenario{vsInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = vsInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)

-- | Validate all pending transactions and notify the wallets
updateAll :: VestingScenario -> Trace [Tx]
updateAll VestingScenario{vsWallets} =
    blockchainActions >>= walletsNotifyBlock vsWallets
