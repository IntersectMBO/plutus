{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
-- | A futures contract in Plutus. This example illustrates three concepts.
--   1. Maintaining a margin (a kind of deposit) during the duration of the contract to protect against breach of contract (see note [Futures in Plutus])
--   2. Using oracle values to obtain current pricing information (see note [Oracles] in Language.Plutus.Runtime)
--   3. Using the redeemer script to model actions that the participants in the contract may take.
module Language.Plutus.Coordination.Contracts.Future(
    -- * Data types
    Future(..),
    FutureData(..),
    FutureRedeemer(..),
    -- * Actions
    initialise,
    settle,
    settleEarly,
    adjustMargin,
    -- * Script
    validatorScript
    ) where

import           Control.Monad              (void)
import           Control.Monad.Error.Class  (MonadError (..))
import qualified Data.Set                   as Set
import           GHC.Generics               (Generic)
import           Language.Plutus.Lift       (makeLift)
import qualified Language.Plutus.Runtime.TH as TH
import           Language.Plutus.TH         (plutus)
import qualified Language.Plutus.TH         as Builtins
import           Wallet.API                 (WalletAPI (..), WalletAPIError, otherError, pubKey, signAndSubmit)
import           Wallet.UTXO                (DataScript (..), TxOutRef', Validator (..), scriptTxIn, scriptTxOut)
import qualified Wallet.UTXO                as UTXO

import           Language.Plutus.Runtime    (Height (..), OracleValue (..), PendingTx (..), PendingTxOut (..),
                                             PendingTxOutType (..), PubKey, Signed (..), ValidatorHash, Value (..))

import           Prelude                    hiding ((&&), (||))

{- note [Futures in Plutus]

A futures contract ("future") is an agreement to change ownership of an
asset at a certain time (the delivery time) for an agreed price (the forward
price). The time of the transfer, and the price, are fixed at the beginning of the contract.

On the mockchain we only have one type of asset (namely, Ada coin value),
so we simply exchange the difference in price between the forward price and the
actual price. This is called a "cash settlement".

The agreement involves two parties, a buyer (long position) and a seller (short
position). At the delivery time the actual price of the asset (spot price) is
quite likely different from the forward price. If the spot price is higher than
the forward price, then the seller transfers the difference to the buyer. If
the spot price is lower than the forward price, then the buyer transfers money
to the seller. In either case there is a risk that the payer does not meet their
obligation (by simply not paying). To protect against this risk, the contract
includes a kind of deposit called "margin".

Each party deposits an initial margin. If the price moves against the seller,
then the seller has to top up their margin periodically (in our case, once each
block). Likewise, if it moves against the buyer then the buyer has to top up
their margin. If either party fails to make a margin payment then the contract
will be settled early.

The current value of the underlying asset is determined by an oracle. See note
[Oracles] in Language.Plutus.Runtime.

-}

-- | Initialise the futures contract by paying the initial margin.
--
initialise :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => PubKey
    -- ^ Identity of the holder of the long position
    -> PubKey
    -- ^ Identity of the holder of the short position
    -> Future
    -> m ()
initialise long short f = do
    let
        im = futureInitialMargin f
        vl = fromIntegral im
        o = scriptTxOut vl (validatorScript f) ds
        ds = DataScript $ UTXO.lifted $ FutureData long short im im

    (payment, change) <- createPaymentWithChange vl
    void $ signAndSubmit payment [o, change]

-- | Close the position by extracting the payment
settle :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => [TxOutRef']
    -> Future
    -> FutureData
    -> OracleValue Value
    -> m ()
settle refs ft fd ov = do
    let
        forwardPrice = futureUnitPrice ft
        OracleValue (Signed (_, (_, spotPrice))) = ov
        delta = (Value $ futureUnits ft) * (spotPrice - forwardPrice)
        longOut = fromIntegral $ futureDataMarginLong fd + delta
        shortOut = fromIntegral $ futureDataMarginShort fd - delta
        red = UTXO.Redeemer $ UTXO.lifted $ Settle ov
        outs = [
            UTXO.pubKeyTxOut longOut (futureDataLong fd),
            UTXO.pubKeyTxOut shortOut (futureDataShort fd)
            ]
        inp = (\r -> scriptTxIn r (validatorScript ft) red) <$> refs
    void $ signAndSubmit (Set.fromList inp) outs

-- | Settle the position early if a margin payment has been missed.
settleEarly :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => [TxOutRef']
    -> Future
    -> FutureData
    -> OracleValue Value
    -> m ()
settleEarly refs ft fd ov = do
    let totalVal = fromIntegral $ futureDataMarginLong fd + futureDataMarginShort fd
        outs = [UTXO.pubKeyTxOut totalVal (futureDataLong fd)]
        inp = (\r -> scriptTxIn r (validatorScript ft) red) <$> refs
        red = UTXO.Redeemer $ UTXO.lifted $ Settle ov
    void $ signAndSubmit (Set.fromList inp) outs

adjustMargin :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => [TxOutRef']
    -> Future
    -> FutureData
    -> UTXO.Value
    -> m ()
adjustMargin refs ft fd vl = do
    pk <- pubKey <$> myKeyPair
    (payment, change) <- createPaymentWithChange vl
    fd' <- let fd''
                | pk == futureDataLong fd = pure $ fd { futureDataMarginLong  = fromIntegral vl + futureDataMarginLong fd  }
                | pk == futureDataShort fd = pure $ fd { futureDataMarginShort = fromIntegral vl + futureDataMarginShort fd }
                | otherwise = otherError "Private key is not part of futures contrat"
            in fd''
    let
        red = UTXO.Redeemer $ UTXO.lifted AdjustMargin
        ds  = DataScript $ UTXO.lifted fd'
        o = scriptTxOut outVal (validatorScript ft) ds
        outVal = vl + fromIntegral (futureDataMarginLong fd + futureDataMarginShort fd)
        inp = Set.fromList $ (\r -> scriptTxIn r (validatorScript ft) red) <$> refs
    void $ signAndSubmit (Set.union payment inp) [o, change]


-- | Basic data of a futures contract. `Future` contains all values that do not
--   change during the lifetime of the contract.
--
data Future = Future {
    futureDeliveryDate  :: Height,
    futureUnits         :: Int,
    futureUnitPrice     :: Value,
    futureInitialMargin :: Value,
    futurePriceOracle   :: PubKey,
    futureMarginPenalty :: Value
    -- ^ How much a participant loses if they fail to make the required margin
    --   payments.
    } deriving Generic

-- | The current "state" of the futures contract. `FutureData` contains values
--   that may change during the lifetime of the contract. This is the data
--   script.
--
data FutureData = FutureData {
    futureDataLong        :: PubKey,
    -- ^ Holder of the long position (buyer)
    futureDataShort       :: PubKey,
    -- ^ Holder of the short position (seller)
    futureDataMarginLong  :: Value,
    -- ^ Current balance of the margin account of the long position
    futureDataMarginShort :: Value
    -- ^ Current balance of the margin account of the short position
    } deriving Generic

-- | Actions that either participant may take. This is the redeemer script.
data FutureRedeemer =
      AdjustMargin
    -- ^ Make a margin payment
    | Settle (OracleValue Value)
    -- ^ Settle the contract
    deriving Generic

validatorScript :: Future -> Validator
validatorScript ft = Validator val where
    val = UTXO.applyScript inner (UTXO.lifted ft)
    inner = UTXO.fromPlcCode $(plutus [|
        \Future{..} (r :: FutureRedeemer) FutureData{..} (p :: (PendingTx ValidatorHash)) ->

            let
                PendingTx _ outs _ _ (Height height) _ ownHash = p

                eqPk :: PubKey -> PubKey -> Bool
                eqPk = $(TH.eqPubKey)

                infixr 3 &&
                (&&) :: Bool -> Bool -> Bool
                (&&) = $(TH.and)

                infixr 3 ||
                (||) :: Bool -> Bool -> Bool
                (||) = $(TH.or)

                forwardPrice :: Int
                forwardPrice = let Value v = futureUnitPrice in v

                marginShort :: Int
                marginShort = let Value v = futureDataMarginShort in v

                marginLong :: Int
                marginLong = let Value v = futureDataMarginLong in v

                penalty :: Int
                penalty = let Value v = futureMarginPenalty in v

                deliveryDate :: Int
                deliveryDate = let Height h = futureDeliveryDate in h

                -- Compute the required margin from the current price of the
                -- underlying asset.
                requiredMargin :: Int -> Int
                requiredMargin spotPrice =
                    let
                        delta  = futureUnits * (spotPrice - forwardPrice)
                    in
                        penalty + delta

                isPubKeyOutput :: PendingTxOut -> PubKey -> Bool
                isPubKeyOutput o k = $(TH.maybe) False ($(TH.eqPubKey) k) ($(TH.pubKeyOutput) o)

                --  | Check if a `PendingTxOut` is a public key output for the given pub. key and value
                paidOutTo :: Int -> PubKey -> PendingTxOut -> Bool
                paidOutTo vl pk txo =
                    let PendingTxOut (Value vl') _ _ = txo in
                    isPubKeyOutput txo pk && vl == vl'

                verifyOracle :: OracleValue a -> (Height, a)
                verifyOracle (OracleValue (Signed (pk, t))) =
                    if pk `eqPk` futurePriceOracle then t else Builtins.error ()

                isValid =
                    case r of

                        -- Settling the contract is allowed if any of three conditions hold:
                        --
                        -- 1. The `deliveryDate` has been reached. In this case both parties get what is left of their margin
                        -- plus/minus the difference between spot and forward price.
                        -- 2. The owner of the long position has failed to make a margin payment. In this case the owner of the short position gets both margins.
                        -- 3. The owner of the short position has failed to make a margin payment. In this case the owner of the long position gets both margins.
                        --
                        -- In case (1) there are two payments (1 to each of the participants). In cases (2) and (3) there is only one payment.

                        Settle ov ->
                            let
                                (_, Value spotPrice) = verifyOracle ov
                                delta  = futureUnits *  (spotPrice - forwardPrice)
                                expShort = marginShort - delta
                                expLong  = marginLong + delta
                                heightvalid = height >= deliveryDate

                                canSettle =
                                    case outs of
                                        o1:o2:_ ->
                                            let paymentsValid =
                                                    (paidOutTo expShort futureDataShort o1 && paidOutTo expLong futureDataLong o2)
                                                    || (paidOutTo expShort futureDataShort o2 && paidOutTo expLong futureDataLong o1)
                                            in
                                                heightvalid && paymentsValid
                                        o1:_ ->
                                            let
                                                totalMargin = marginShort + marginLong
                                                case2 = marginLong < requiredMargin spotPrice
                                                        && paidOutTo totalMargin futureDataShort o1

                                                case3 = marginShort < requiredMargin spotPrice
                                                        && paidOutTo totalMargin futureDataLong o1

                                            in
                                                case2 || case3
                                        _ -> False

                            in
                               canSettle

                        -- For adjusting the margin we simply check that the amount locked in the contract
                        -- is larger than it was before.
                        --
                        AdjustMargin ->
                            case outs of
                                ot:_ ->
                                    case ot of
                                        PendingTxOut (Value v) (Just (vh, _)) DataTxOut ->
                                            v > marginShort + marginLong
                                            && $(TH.eqValidator) vh ownHash
                                        _ -> True

                                _ -> False
            in
                if isValid then () else Builtins.error ()
            |])

makeLift ''Future
makeLift ''FutureData
makeLift ''FutureRedeemer
