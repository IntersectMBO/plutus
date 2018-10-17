{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
module Spec.Vesting(tests) where

import           Control.Monad                                  (void)
import           Data.Either                                    (isRight)
import           Data.Foldable                                  (traverse_)
import qualified Data.Map                                       as Map
import           Hedgehog                                       (Property, forAll, property)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog                            (testProperty)

import           Language.Plutus.Coordination.Contracts.Vesting (Vesting (..), VestingData (..), VestingTranche (..),
                                                                 retrieveFunds, totalAmount, vestFunds)
import qualified Language.Plutus.Runtime                        as Runtime
import           Wallet.API                                     (PubKey (..))
import           Wallet.Emulator                                hiding (Value)
import qualified Wallet.Generators                              as Gen
import qualified Wallet.UTXO                                    as UTXO


tests :: TestTree
tests = testGroup "vesting" [
    testProperty "secure some funds with the vesting script" secureFunds,
    testProperty "retrieve some funds" canRetrieveFunds,
    testProperty "cannot retrieve more than allowed" cannotRetrieveTooMuch,
    testProperty "can retrieve everything at end" canRetrieveFundsAtEnd
    ]

-- | Commit some funds from a wallet to a vesting scheme. Returns the reference
--   to the transaction output that is locked by the schemes's validator
--   script (and can be collected by the scheme's owner)
commit :: Wallet -> Vesting -> Runtime.Value -> Trace EmulatedWalletApi  TxOutRef'
commit w vv vl = exScriptOut <$> walletAction w (void $ vestFunds vv vl) where
    exScriptOut = snd . head . filter (isPayToScriptOut . fst) . txOutRefs . head

secureFunds :: Property
secureFunds = checkVestingTrace scen1 $ do
    let VestingScenario s [w1, w2] _ _ = scen1
        updateAll' = updateAll scen1
    updateAll'
    _ <- commit w2 s total
    updateAll'
    traverse_ (uncurry assertOwnFundsEq) [(w2, w2Funds), (w1, startingBalance)]

canRetrieveFunds :: Property
canRetrieveFunds = checkVestingTrace scen1 $ do
    let VestingScenario s [w1, w2] _ _ = scen1
        updateAll' = updateAll scen1
    updateAll'
    ref <- commit w2 s total
    updateAll'
    addBlocks 10
    let ds = VestingData (vsScriptHash scen1) 150
    -- Take 150 out of the scheme
    walletAction w1 $ void (retrieveFunds s ds ref 150)
    updateAll'
    traverse_ (uncurry assertOwnFundsEq) [(w2, w2Funds), (w1, startingBalance + 150)]

cannotRetrieveTooMuch :: Property
cannotRetrieveTooMuch = checkVestingTrace scen1 $ do
    let VestingScenario s [w1, w2] _ _ = scen1
        updateAll' = updateAll scen1
    updateAll'
    ref <- commit w2 s total
    updateAll'
    addBlocks 10
    -- at block height 11, not more than 200 may be taken out
    let ds = VestingData (vsScriptHash scen1) 250
    walletAction w1 $ void (retrieveFunds s ds ref 250)
    updateAll'
    traverse_ (uncurry assertOwnFundsEq) [(w2, w2Funds), (w1, startingBalance)]

canRetrieveFundsAtEnd :: Property
canRetrieveFundsAtEnd = checkVestingTrace scen1 $ do
    let VestingScenario s [w1, w2] _ _ = scen1
        updateAll' = updateAll scen1
    updateAll'
    ref <- commit w2 s total
    updateAll'
    -- everything can be taken out at h=21
    addBlocks 20
    let ds = VestingData (vsScriptHash scen1) 600
    walletAction w1 $ void (retrieveFunds s ds ref 600)
    updateAll'
    traverse_ (uncurry assertOwnFundsEq) [(w2, w2Funds), (w1, startingBalance + fromIntegral total)]

-- | Vesting scenario with test parameters
data VestingScenario = VestingScenario {
    vsVestingScheme   :: Vesting,
    vsWallets         :: [Wallet],
    vsInitialBalances :: Map.Map PubKey UTXO.Value,
    vsScriptHash      :: Runtime.Hash -- Hash of validator script for this scenario [CGP-400]
    }

scen1 :: VestingScenario
scen1 = VestingScenario{..} where
    vsVestingScheme = Vesting {
        vestingTranche1 = VestingTranche 10 200,
        vestingTranche2 = VestingTranche 20 400,
        vestingOwner    = PubKey 1 }
    vsWallets = Wallet <$> [1, 2]
    vsInitialBalances = Map.fromList [
        (PubKey 1, startingBalance),
        (PubKey 2, startingBalance)]
    vsScriptHash = 1123

-- | Funds available to each wallet after the initial transaction on the
--   mockchain
startingBalance :: UTXO.Value
startingBalance = 1000

-- | Amount of money left in wallet `Wallet 2` after committing funds to the
--   vesting scheme
w2Funds :: UTXO.Value
w2Funds = startingBalance - fromIntegral total

-- | Total amount of money vested in the scheme `scen1`
total :: Runtime.Value
total = totalAmount $ vsVestingScheme scen1

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkVestingTrace :: VestingScenario -> Trace EmulatedWalletApi () -> Property
checkVestingTrace VestingScenario{vsInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = vsInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)

-- | Validate all pending transactions and notify the wallets
updateAll :: VestingScenario -> Trace EmulatedWalletApi [Tx]
updateAll VestingScenario{vsWallets} =
    blockchainActions >>= walletsNotifyBlock vsWallets
