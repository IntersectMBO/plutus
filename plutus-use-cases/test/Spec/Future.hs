{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
module Spec.Future(tests) where

import           Control.Monad                                   (void)
import           Data.Either                                     (isRight)
import           Data.Foldable                                   (traverse_)
import qualified Data.Map                                        as Map
import           Hedgehog                                        (Property, forAll, property)
import qualified Hedgehog
import qualified Spec.Size                                       as Size
import           Test.Tasty
import           Test.Tasty.Hedgehog                             (testProperty)
import qualified Test.Tasty.HUnit                                as HUnit

import qualified Ledger
import           Ledger.Ada                                      (Ada)
import qualified Ledger.Ada                                      as Ada
import           Ledger.Validation                               (OracleValue (..))
import qualified Ledger.Value                                    as Value
import           Prelude                                         hiding (init)
import           Wallet.API                                      (PubKey (..))
import           Wallet.Emulator
import qualified Wallet.Emulator.Generators                      as Gen
import qualified Wallet.Generators                               as Gen

import           Language.PlutusTx.Coordination.Contracts.Future (Future (..), FutureData (..))
import qualified Language.PlutusTx.Coordination.Contracts.Future as F

-- | Wallet 1. Holder of the "long" position in the contract.
wallet1 :: Wallet
wallet1 = Wallet 1

-- | Wallet 2. Holder of the "short" position in the contract.
wallet2 :: Wallet
wallet2 = Wallet 2

tests :: TestTree
tests = testGroup "futures" [
    testProperty "commit initial margin" initialiseFuture,
    testProperty "close the position" settle,
    testProperty "close early if margin payment was missed" settleEarly,
    testProperty "increase the margin" increaseMargin,
    HUnit.testCase "script size is reasonable" (Size.reasonable (F.validatorScript contract) 50000)
    ]

init :: Wallet -> Trace MockWallet Ledger.TxOutRef
init w = outp <$> walletAction w (F.initialise (walletPubKey wallet1) (walletPubKey wallet2) contract) where
    outp = snd . head . filter (Ledger.isPayToScriptOut . fst) . Ledger.txOutRefs . head

adjustMargin :: Wallet -> [Ledger.TxOutRef] -> FutureData -> Ada -> Trace MockWallet Ledger.TxOutRef
adjustMargin w refs fd vl =
    outp <$> walletAction w (F.adjustMargin refs contract fd vl) where
        outp = snd . head . filter (Ledger.isPayToScriptOut . fst) . Ledger.txOutRefs . head

-- | Initialise the futures contract with contributions from wallets 1 and 2,
--   and update all wallets. Running `initBoth` will increase the slot number
--   by 2.
initBoth :: Trace MockWallet [Ledger.TxOutRef]
initBoth = do
    updateAll
    ins <- traverse init [wallet1, wallet2]
    updateAll
    return ins


initialiseFuture :: Property
initialiseFuture = checkTrace $ do
    void initBoth
    traverse_ (uncurry assertOwnFundsEq) [
        (wallet1, Value.minus startingBalance (Ada.toValue initMargin)),
        (wallet2, Value.minus startingBalance (Ada.toValue initMargin))]

settle :: Property
settle = checkTrace $ do
    ins <- initBoth
    let
        im = initMargin
        cur = FutureData (walletPubKey wallet1) (walletPubKey wallet2) im im
        spotPrice = 1124
        delta = fromIntegral units * (spotPrice - forwardPrice)
        ov  = OracleValue oracle (Ledger.Slot 10) spotPrice

    -- advance the clock to slot 10
    void $ addBlocks 8
    void $ walletAction wallet2 (F.settle ins contract cur ov)
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (wallet1, Value.plus  startingBalance (Ada.toValue delta)),
        (wallet2, Value.minus startingBalance (Ada.toValue delta))]

settleEarly :: Property
settleEarly = checkTrace $ do
    ins <- initBoth
    let
        im = initMargin
        cur = FutureData (walletPubKey wallet1) (walletPubKey wallet2) im im

        -- In this example, the price moves up (in favour of the long position)
        -- Wallet 2 fails to make the required margin payment, so wallet 1
        -- can the entire margin of wallet 2, including the penalty fee.
        -- This illustrates how the participants are incentivised to keep
        -- up with the variation margin.
        (_, upper) = marginRange
        spotPrice = upper + 1
        ov  = OracleValue oracle (Ledger.Slot 8) spotPrice

    -- advance the clock to slot 8
    void $ addBlocks 6
    void $ walletAction wallet1 (F.settleEarly ins contract cur ov)
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (wallet1, Value.plus  startingBalance (Ada.toValue initMargin)),
        (wallet2, Value.minus startingBalance (Ada.toValue initMargin))]

increaseMargin :: Property
increaseMargin = checkTrace $ do
    ins <- initBoth
    let
        im = initMargin
        cur = FutureData (walletPubKey wallet1) (walletPubKey wallet2) im im
        increase = fromIntegral units * 5

    -- advance the clock to slot 8
    void $ addBlocks 6

    -- Commit an additional `units * 5` amount of funds
    ins' <- adjustMargin wallet2 ins cur increase
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (wallet2, Value.minus startingBalance (Ada.toValue (initMargin + increase)))]
    -- advance the clock to slot 10
    void $ addBlocks 2

    -- Now the contract has ended successfully and wallet 2 gets some of its
    -- margin back.
    let
        im' = initMargin + increase
        cur' = cur { futureDataMarginShort = im' }

        (_, upper) = marginRange
        -- Note that this price would have caused the contract to end
        -- prematurely if it hadn't been for the increase (compare with
        -- settleEarly above)
        spotPrice = upper + 1

        delta = fromIntegral units * (spotPrice - forwardPrice)
        ov  = OracleValue oracle (Ledger.Slot 10) spotPrice

    void $ walletAction wallet2 (F.settle [ins'] contract cur' ov)
    updateAll

    -- NOTE: At this point, (initMargin - penalty) < delta < im'
    --       Meaning that it is still more profitable for wallet 2
    --       to see the contract through (via `settle`) than to
    --       simply ignore it and hence lose its entire margin im'.
    traverse_ (uncurry assertOwnFundsEq) [
        (wallet1, Value.plus  startingBalance (Ada.toValue delta)),
        (wallet2, Value.minus startingBalance (Ada.toValue delta))]

-- | A futures contract over 187 units with a forward price of 1233, due at
--   10 blocks.
contract :: Future
contract = Future {
    futureDeliveryDate  = Ledger.Slot 10,
    futureUnits         = units,
    futureUnitPrice     = forwardPrice,
    futureInitialMargin = im,
    futurePriceOracle   = oracle,
    futureMarginPenalty = penalty
    } where
        im = penalty + (Ada.fromInt units * forwardPrice `div` 20) -- 5%

-- | Margin penalty
penalty :: Ada
penalty = 1000

-- | The forward price agreed at the beginning of the contract.
forwardPrice :: Ada
forwardPrice = 1123

-- | Range within which the underlying asset's price can move before the first
--   margin payment is necessary.
--   If the price approaches the lower range, then the buyer (long position,
--   Wallet 1) has to increase their margin, and vice versa.
marginRange :: (Ada, Ada)
marginRange = (forwardPrice - delta, forwardPrice + delta) where
    delta = forwardPrice `div` 20

-- | How many units of the underlying asset are covered by the contract.
units :: Integer
units = 187

oracle :: PubKey
oracle = walletPubKey (Wallet 3)

initMargin :: Ada
initMargin = futureInitialMargin contract

-- | Funds available to wallets at the beginning.
startingBalance :: Ledger.Value
startingBalance = Ada.adaValueOf 1000000

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkTrace :: Trace MockWallet () -> Property
checkTrace t = property $ do
    let
        ib = Map.fromList [(walletPubKey wallet1, startingBalance), (walletPubKey wallet2, startingBalance)]
        model = Gen.generatorModel { Gen.gmInitialBalance = ib }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == _txPool st)

-- | Validate all pending transactions and notify all wallets
updateAll :: Trace MockWallet ()
updateAll =
    processPending >>= void . walletsNotifyBlock [wallet1, wallet2]
