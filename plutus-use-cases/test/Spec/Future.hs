{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
module Spec.Future(tests) where

import           Control.Monad                                 (void)
import           Data.Either                                   (isRight)
import           Data.Foldable                                 (traverse_)
import qualified Data.Map                                      as Map
import           Hedgehog                                      (Property, forAll, property)
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog                           (testProperty)

import           Prelude                                       hiding (init)
import           Wallet.API                                    (PubKey (..))
import           Wallet.Emulator                               hiding (Value)
import qualified Wallet.Generators                             as Gen
import qualified Wallet.UTXO                                   as UTXO
import           Wallet.UTXO.Runtime                           (OracleValue (..), Signed (..))
import qualified Wallet.UTXO.Runtime                           as Runtime

import           Language.Plutus.Coordination.Contracts.Future (Future (..), FutureData (..))
import qualified Language.Plutus.Coordination.Contracts.Future as F

tests :: TestTree
tests = testGroup "futures" [
    testProperty "commit initial margin" initialiseFuture,
    testProperty "close the position" settle,
    testProperty "close early if margin payment was missed" settleEarly,
    testProperty "increase the margin" increaseMargin
    ]

init :: Wallet -> Trace EmulatedWalletApi TxOutRef'
init w = outp <$> walletAction w (F.initialise (PubKey 1) (PubKey 2) contract) where
    outp = snd . head . filter (isPayToScriptOut . fst) . txOutRefs . head

adjustMargin :: Wallet -> [TxOutRef'] -> FutureData -> UTXO.Value -> Trace EmulatedWalletApi TxOutRef'
adjustMargin w refs fd vl =
    outp <$> walletAction w (F.adjustMargin refs contract fd vl) where
        outp = snd . head . filter (isPayToScriptOut . fst) . txOutRefs . head

-- | Initialise the futures contract with contributions from wallets 1 and 2,
--   and update all wallets. Running `initBoth` will increase the block height
--   by 2.
initBoth :: Trace EmulatedWalletApi [TxOutRef']
initBoth = do
    updateAll
    ins <- traverse init [w1, w2]
    updateAll
    return ins


initialiseFuture :: Property
initialiseFuture = checkTrace $ do
    void initBoth
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, startingBalance - initMargin),
        (w2, startingBalance - initMargin)]

settle :: Property
settle = checkTrace $ do
    ins <- initBoth
    let
        im = fromIntegral initMargin
        cur = FutureData (PubKey 1) (PubKey 2) im im
        spotPrice = 1124
        delta = fromIntegral $ units * (spotPrice - forwardPrice)
        ov  = OracleValue (Signed (oracle, (10, spotPrice)))

    -- advance the clock to block height 10
    void $ addBlocks 8
    void $ walletAction w2 (F.settle ins contract cur ov)
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, startingBalance + delta),
        (w2, startingBalance - delta)]

settleEarly :: Property
settleEarly = checkTrace $ do
    ins <- initBoth
    let
        im = fromIntegral initMargin
        cur = FutureData (PubKey 1) (PubKey 2) im im

        -- In this example, the price moves up (in favour of the long position)
        -- Wallet 2 fails to make the required margin payment, so wallet 1
        -- can the entire margin of wallet 2, including the penalty fee.
        -- This illustrates how the participants are incentivised to keep
        -- up with the variation margin.
        (_, upper) = marginRange
        spotPrice = upper + 1
        ov  = OracleValue (Signed (oracle, (8, spotPrice)))

    -- advance the clock to block height 8
    void $ addBlocks 6
    void $ walletAction w1 (F.settleEarly ins contract cur ov)
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, startingBalance + initMargin),
        (w2, startingBalance - initMargin)]

increaseMargin :: Property
increaseMargin = checkTrace $ do
    ins <- initBoth
    let
        im = fromIntegral initMargin
        cur = FutureData (PubKey 1) (PubKey 2) im im
        increase = fromIntegral units * 5

    -- advance the clock to block height 8
    void $ addBlocks 6

    -- Commit an additional `units * 5` amount of funds
    ins' <- adjustMargin w2 ins cur increase
    updateAll
    traverse_ (uncurry assertOwnFundsEq) [(w2, startingBalance - (initMargin + increase))]
    -- advance the clock to block height 10
    void $ addBlocks 2

    -- Now the contract has ended successfully and wallet 2 gets some of its
    -- margin back.
    let
        im' = fromIntegral $ initMargin + increase
        cur' = cur { futureDataMarginShort = im' }

        (_, upper) = marginRange
        -- Note that this price would have caused the contract to end
        -- prematurely if it hadn't been for the increase (compare with
        -- settleEarly above)
        spotPrice = upper + 1

        delta = fromIntegral $ units * (spotPrice - forwardPrice)
        ov  = OracleValue (Signed (oracle, (10, spotPrice)))

    void $ walletAction w2 (F.settle [ins'] contract cur' ov)
    updateAll

    -- NOTE: At this point, (initMargin - penalty) < delta < im'
    --       Meaning that it is still more profitable for wallet 2
    --       to see the contract through (via `settle`) than to
    --       simply ignore it and hence lose its entire margin im'.
    traverse_ (uncurry assertOwnFundsEq) [
        (w1, startingBalance + delta),
        (w2, startingBalance - delta)]

-- | A futures contract over 187 units with a forward price of 1233, due at
--   10 blocks.
contract :: Future
contract = Future {
    futureDeliveryDate  = 10,
    futureUnits         = units,
    futureUnitPrice     = forwardPrice,
    futureInitialMargin = im,
    futurePriceOracle   = oracle,
    futureMarginPenalty = penalty
    } where
        im = penalty + (units * forwardPrice `div` 20) -- 5%

-- | Margin penalty
penalty :: Runtime.Value
penalty = 1000

-- | The forward price agreed at the beginning of the contract.
forwardPrice :: Runtime.Value
forwardPrice = 1123

-- | Range within which the underlying asset's price can move before the first
--   margin payment is necessary.
--   If the price approaches the lower range, then the buyer (long position,
--   Wallet 1) has to increase their margin, and vice versa.
marginRange :: (Runtime.Value, Runtime.Value)
marginRange = (forwardPrice - delta, forwardPrice + delta) where
    delta = forwardPrice `div` 20

-- | How many units of the underlying asset are covered by the contract.
units :: Int
units = 187

-- | Wallet 1. Holder of the "long" position in the contract.
w1 :: Wallet
w1 = Wallet 1

-- | Wallet 2. Holder of the "short" position in the contract.
w2 :: Wallet
w2 = Wallet 2

oracle :: PubKey
oracle = PubKey 17

initMargin :: UTXO.Value
initMargin = fromIntegral $ futureInitialMargin contract

-- | Funds available to wallets at the beginning.
startingBalance :: UTXO.Value
startingBalance = 1000000

-- | Run a trace with the given scenario and check that the emulator finished
--   successfully with an empty transaction pool.
checkTrace :: Trace EmulatedWalletApi () -> Property
checkTrace t = property $ do
    let
        ib = Map.fromList [(PubKey 1, startingBalance), (PubKey 2, startingBalance)]
        model = Gen.generatorModel { Gen.gmInitialBalance = ib }
    (result, st) <- forAll $ Gen.runTraceOn model t
    Hedgehog.assert (isRight result)
    Hedgehog.assert ([] == emTxPool st)

-- | Validate all pending transactions and notify all wallets
updateAll :: Trace EmulatedWalletApi ()
updateAll =
    blockchainActions >>= void . walletsNotifyBlock [w1, w2]
