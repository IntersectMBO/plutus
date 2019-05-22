{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-unused-do-bind #-}
module Spec.Vesting(tests) where

import           Control.Monad                                    (void)
import           Control.Monad.IO.Class
import           Data.Either                                      (isRight)
import           Data.Foldable                                    (traverse_)
import qualified Data.Map                                         as Map
import           Hedgehog                                         (Property, forAll, property)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog                              (testProperty)
import qualified Test.Tasty.HUnit                                 as HUnit

import           Language.PlutusTx.Coordination.Contracts.Vesting (Vesting (..), VestingData (..), VestingTranche (..),
                                                                   retrieveFunds, totalAmount, validatorScript,
                                                                   validatorScriptHash, vestFunds)
import qualified Ledger
import qualified Ledger.Ada                                       as Ada
import qualified Ledger.Validation                                as Validation
import           Ledger.Value                                     (Value)
import qualified Ledger.Value                                     as Value
import           Wallet                                           (PubKey (..))
import           Wallet.Emulator
import qualified Wallet.Emulator.Generators                       as Gen
import qualified Wallet.Generators                                as Gen

w1, w2 :: Wallet
w1 = Wallet 1
w2 = Wallet 2

tests :: TestTree
tests = testGroup "vesting" [
    testProperty "secure some funds with the vesting script" secureFunds,
    testProperty "retrieve some funds" canRetrieveFunds,
    testProperty "cannot retrieve more than allowed" cannotRetrieveTooMuch,
    testProperty "can retrieve everything at end" canRetrieveFundsAtEnd,
    HUnit.testCase "script size is reasonable" size
    ]

size :: HUnit.Assertion
size = do
    let Ledger.ValidatorScript s = validatorScript (vsVestingScheme scen1)
    let sz = Ledger.scriptSize s
    -- so the actual size is visible in the log
    liftIO $ putStrLn ("Script size: " ++ show sz)
    HUnit.assertBool "script too big" (sz <= 45000)

-- | The scenario used in the property tests. It sets up a vesting scheme for a
--   total of 600 ada over 20 blocks (200 ada can be taken out before that, at
--   10 blocks).
scen1 :: VestingScenario
scen1 = VestingScenario{..} where
    vsVestingScheme = Vesting {
        vestingTranche1 = VestingTranche (Ledger.Slot 10) (Ada.adaValueOf 200),
        vestingTranche2 = VestingTranche (Ledger.Slot 20) (Ada.adaValueOf 400),
        vestingOwner    = walletPubKey w1 }
    vsInitialBalances = Map.fromList [
        (walletPubKey w1, startingBalance),
        (walletPubKey w2, startingBalance)]
    vsScriptHash = validatorScriptHash vsVestingScheme

-- | Commit some funds from a wallet to a vesting scheme. Returns the reference
--   to the transaction output that is locked by the schemes's validator
--   script (and can be collected by the scheme's owner)
commit :: Wallet -> Vesting -> Value -> Trace MockWallet Ledger.TxOutRef
commit w vv vl = exScriptOut <$> walletAction w (void $ vestFunds vv vl) where
    exScriptOut = snd . head . filter (Ledger.isPayToScriptOut . fst) . Ledger.txOutRefs . head

secureFunds :: Property
secureFunds = checkVestingTrace scen1 $ do
    let VestingScenario s _ _ = scen1
    updateAll
    _ <- commit w2 s total
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w2, w2Funds),
        (w1, startingBalance)]

canRetrieveFunds :: Property
canRetrieveFunds = checkVestingTrace scen1 $ do
    let VestingScenario s _ _ = scen1
        amt = Ada.adaValueOf 150
    updateAll

    -- Wallet 2 locks 600 ada under the scheme described in `scen1`
    ref <- commit w2 s total
    updateAll

    -- Advance the clock so that the first tranche (200 ada) becomes unlocked.
    addBlocks' 10
    let ds = VestingData (vsScriptHash scen1) amt

    -- Take 150 ada out of the scheme
    walletAction w1 $ void (retrieveFunds s ds ref amt)
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w2, w2Funds),
        (w1, Value.plus startingBalance amt)]

cannotRetrieveTooMuch :: Property
cannotRetrieveTooMuch = checkVestingTrace scen1 $ do
    let VestingScenario s _ _ = scen1
    updateAll
    ref <- commit w2 s total
    updateAll
    addBlocks' 10

    -- at slot 11, not more than 200 may be taken out
    -- so the transaction submitted by `retrieveFunds` below
    -- is invalid and will be rejected by the mockchain.
    let ds = VestingData (vsScriptHash scen1) (Ada.adaValueOf 250)
    walletAction w1 $ void (retrieveFunds s ds ref (Ada.adaValueOf 250))
    updateAll

    -- The funds of both wallets should be unchanged.
    traverse_ (uncurry assertOwnFundsEq) [(w2, w2Funds), (w1, startingBalance)]

canRetrieveFundsAtEnd :: Property
canRetrieveFundsAtEnd = checkVestingTrace scen1 $ do
    let VestingScenario s _ _ = scen1
    updateAll
    ref <- commit w2 s total
    updateAll
    addBlocks' 20

    -- everything can be taken out at h=21
    let ds = VestingData (vsScriptHash scen1) (Ada.adaValueOf 600)
    walletAction w1 $ void (retrieveFunds s ds ref (Ada.adaValueOf 600))
    updateAll

    -- Wallet 1 now has control of all the funds that were locked in the
    -- vesting scheme.
    traverse_ (uncurry assertOwnFundsEq) [
        (w2, w2Funds),
        (w1, Value.plus startingBalance total)]

-- | Vesting scenario with test parameters
data VestingScenario = VestingScenario {
    vsVestingScheme   :: Vesting,
    vsInitialBalances :: Map.Map PubKey Ledger.Value,
    vsScriptHash      :: Validation.ValidatorHash -- Hash of validator script for this scenario
    }

-- | Funds available to each wallet after the initial transaction on the
--   mockchain
startingBalance :: Ledger.Value
startingBalance = Ada.adaValueOf 1000

-- | Amount of money left in wallet `Wallet 2` after committing funds to the
--   vesting scheme
w2Funds :: Ledger.Value
w2Funds = Value.minus startingBalance total

-- | Total amount of money vested in the scheme `scen1`
total :: Value
total = totalAmount $ vsVestingScheme scen1

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkVestingTrace :: VestingScenario -> Trace MockWallet () -> Property
checkVestingTrace VestingScenario{vsInitialBalances} t = property $ do
    let model = Gen.generatorModel { Gen.gmInitialBalance = vsInitialBalances }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)

-- | Validate all pending transactions and notify the wallets
updateAll :: Trace MockWallet [Ledger.Tx]
updateAll =
    processPending >>= walletsNotifyBlock [w1, w2]

-- | Add a number of blocks and notify the wallets
addBlocks' :: Int -> Trace MockWallet ()
addBlocks' i = traverse_ (const updateAll) [1..i]
