{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | The interface between the wallet and Plutus client code.
module Wallet.API(
    WalletEffect,
    submitTxn,
    ownPubKey,
    updatePaymentWithChange,
    walletSlot,
    ownOutputs,
    NodeClientEffect,
    publishTx,
    getClientSlot,
    SigningProcessEffect,
    addSignatures,
    ChainIndexEffect,
    startWatching,
    watchedAddresses,
    PubKey(..),
    createPaymentWithChange,
    createTxAndSubmit,
    signTxAndSubmit,
    signTxAndSubmit_,
    signWithOwnPublicKey,
    payToScript,
    payToScript_,
    payToPublicKey,
    payToPublicKey_,
    payToScripts,
    payToScripts_,
    getScriptInputs,
    getScriptInputsFilter,
    collectFromScript,
    collectFromScriptTxn,
    spendScriptOutputs,
    ownPubKeyTxOut,
    outputsAt,
    -- * Slot ranges
    Interval(..),
    Slot,
    SlotRange,
    width,
    defaultSlotRange,
    interval,
    intervalFrom,
    intervalTo,
    singleton,
    isEmpty,
    always,
    member,
    before,
    after,
    contains,
    -- * Error handling
    WalletAPIError(..),
    throwInsufficientFundsError,
    throwOtherError,
    ) where

import           Control.Lens              hiding (contains)
import           Control.Monad             (void, when)
import           Control.Monad.Freer
import           Control.Monad.Freer.Log   (Log, logWarn)
import           Data.Foldable             (fold)
import qualified Data.Map                  as Map
import           Data.Maybe                (fromMaybe, mapMaybe, maybeToList)
import qualified Data.Set                  as Set
import qualified Data.Text                 as Text
import           Data.Text.Prettyprint.Doc hiding (width)
import           Ledger                    hiding (inputs, out, value)
import           Ledger.AddressMap         (AddressMap)
import qualified Ledger.Interval           as Interval
import qualified Ledger.Value              as Value
import           Wallet.Effects
import           Wallet.Emulator.Error

import           Prelude                   hiding (Ordering (..))

createPaymentWithChange :: Member WalletEffect effs => Value -> Eff effs (Set.Set TxIn, Maybe TxOut)
createPaymentWithChange v =
    let pmt = Payment{paymentInputs=Set.empty, paymentChangeOutput = Nothing} in
    do
        Payment{paymentInputs, paymentChangeOutput} <- updatePaymentWithChange v pmt
        pure (paymentInputs, paymentChangeOutput)

-- | Transfer some funds to a number of script addresses, returning the
-- transaction that was submitted.
payToScripts ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => SlotRange -> [(Address, Value, Datum)] -> Eff effs Tx
payToScripts range ins = do
    let
        totalVal     = fold $ fmap (view _2) ins
        otherOutputs = fmap (\(addr, vl, ds) -> TxOut addr vl (PayToScript (datumHash ds))) ins
        datas        = fmap (\(_, _, d) -> d) ins
    (i, ownChange) <- createPaymentWithChange totalVal
    createTxAndSubmit range i (maybe otherOutputs (:otherOutputs) ownChange) datas

-- | Transfer some funds to a number of script addresses.
payToScripts_ ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => SlotRange -> [(Address, Value, Datum)] -> Eff effs ()
payToScripts_ range = void . payToScripts range

-- | Transfer some funds to an address locked by a script, returning the
--   transaction that was submitted.
payToScript ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => SlotRange -> Address -> Value -> Datum -> Eff effs Tx
payToScript range addr v ds = payToScripts range [(addr, v, ds)]

-- | Transfer some funds to an address locked by a script.
payToScript_ ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => SlotRange -> Address -> Value -> Datum -> Eff effs ()
payToScript_ range addr v = void . payToScript range addr v

getScriptInputs
    :: AddressMap
    -> Validator
    -> Redeemer
    -> [(TxIn, Value)]
getScriptInputs = getScriptInputsFilter (\_ _ -> True)

getScriptInputsFilter
    :: (TxOutRef -> TxOutTx -> Bool)
    -> AddressMap
    -> Validator
    -> Redeemer
    -> [(TxIn, Value)]
getScriptInputsFilter flt am vls red =
    let utxo    = fromMaybe Map.empty $ am ^. at (scriptAddress vls)
        ourUtxo = Map.filterWithKey flt utxo
        mkIn :: TxOutRef -> Datum -> TxIn
        mkIn ref = scriptTxIn ref vls red
        inputs =
            fmap (\(ref, dat, val) -> (mkIn ref dat, val)) $
            mapMaybe (\(ref, out) -> (ref,,txOutValue $ txOutTxOut out) <$> txOutTxDatum out) $
            Map.toList ourUtxo
    in inputs

spendScriptOutputs ::
    ( Member ChainIndexEffect effs
    ) => Validator -> Redeemer -> Eff effs [(TxIn, Value)]
spendScriptOutputs = spendScriptOutputsFilter (\_ _ -> True)

-- | Take all known outputs at an 'Address' and spend them using the
--   validator and redeemer scripts.
spendScriptOutputsFilter ::
    ( Member ChainIndexEffect effs
    )
    => (TxOutRef -> TxOutTx -> Bool)
    -> Validator
    -> Redeemer
    -> Eff effs [(TxIn, Value)]
spendScriptOutputsFilter flt vls red = do
    am <- watchedAddresses
    pure $ getScriptInputsFilter flt am vls red

-- | Collect all unspent outputs from a pay to script address and transfer them
--   to a public key owned by us.
collectFromScript ::
    ( Members WalletEffects effs
    , Member Log effs
    )
    => SlotRange -> Validator -> Redeemer -> Eff effs ()
collectFromScript = collectFromScriptFilter (\_ _ -> True)

-- | Given the pay to script address of the 'Validator', collect from it
--   all the outputs that were produced by a specific transaction, using the
--   'Redeemer'.
collectFromScriptTxn ::
    ( Members WalletEffects effs
    , Member Log effs
    )
    => SlotRange
    -> Validator
    -> Redeemer
    -> TxId
    -> Eff effs ()
collectFromScriptTxn range vls red txid =
    let flt k _ = txid == Ledger.txOutRefId k in
    collectFromScriptFilter flt range vls red

-- | Given the pay to script address of the 'Validator', collect from it
--   all the outputs that match a predicate, using the 'Redeemer'.
collectFromScriptFilter ::
    ( Members WalletEffects effs
    , Member Log effs)
    => (TxOutRef -> TxOutTx -> Bool)
    -> SlotRange
    -> Validator
    -> Redeemer
    -> Eff effs ()
collectFromScriptFilter flt range vls red = do
    inputsWithValues <- spendScriptOutputsFilter flt vls red
    let adr     = Ledger.scriptAddress vls
        inputs = Set.fromList $ fmap fst inputsWithValues
        value  = foldMap snd inputsWithValues

    out <- ownPubKeyTxOut value
    warnEmptyTransaction value adr
    void $ createTxAndSubmit range inputs [out] []

-- | Transfer some funds to an address locked by a public key, returning the
--   transaction that was submitted.
payToPublicKey ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => SlotRange -> Value -> PubKey -> Eff effs Tx
payToPublicKey range v pk = do
    (i, own) <- createPaymentWithChange v
    let other = pubKeyTxOut v pk
    createTxAndSubmit range i (other : maybeToList own) []

-- | Transfer some funds to an address locked by a public key.
payToPublicKey_ ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => SlotRange -> Value -> PubKey -> Eff effs ()
payToPublicKey_ r v = void . payToPublicKey r v

-- | Create a `TxOut` that pays to the public key owned by us.
ownPubKeyTxOut :: Member WalletEffect effs => Value -> Eff effs TxOut
ownPubKeyTxOut v = pubKeyTxOut v <$> ownPubKey

-- | Retrieve the unspent transaction outputs known to the wallet at an adresss.
outputsAt :: (Member ChainIndexEffect effs) => Address -> Eff effs (Map.Map Ledger.TxOutRef TxOutTx)
outputsAt adr = fmap (\utxos -> fromMaybe Map.empty $ utxos ^. at adr) watchedAddresses

-- | Create a transaction, sign it with the wallet's private key, and submit it.
--   TODO: This is here to make the calculation of fees easier for old-style contracts
--         and should be removed when all contracts have been ported to the new API.
createTxAndSubmit ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => SlotRange
    -> Set.Set TxIn
    -> [TxOut]
    -> [Datum]
    -> Eff effs Tx
createTxAndSubmit range ins outs datas = do
    let tx = mempty
            { txInputs = ins
            , txOutputs = outs
            , txValidRange = range
            , txData = Map.fromList $ fmap (\ds -> (datumHash ds, ds)) datas
            }
    signTxAndSubmit $ tx { txFee = minFee tx }

-- | Add the signature of the user's public key to the transaction
signWithOwnPublicKey ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => Tx -> Eff effs Tx
signWithOwnPublicKey t = do
    pk <- ownPubKey
    addSignatures [pubKeyHash pk] t

-- | Add the wallet's signature to the transaction and submit it. Returns
--   the transaction with the wallet's signature.
signTxAndSubmit ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => Tx -> Eff effs Tx
signTxAndSubmit t = do
    pk <- ownPubKey
    tx' <- addSignatures [pubKeyHash pk] t
    submitTxn tx'
    pure tx'

-- | A version of 'signTxAndSubmit' that discards the result.
signTxAndSubmit_ ::
    ( Member WalletEffect effs
    , Member SigningProcessEffect effs
    )
    => Tx -> Eff effs ()
signTxAndSubmit_ = void . signTxAndSubmit

-- | The default slot validity range for transactions.
defaultSlotRange :: SlotRange
defaultSlotRange = always

-- | See 'Interval.from'.
intervalFrom :: a -> Interval a
intervalFrom = Interval.from

-- | See 'Interval.to'.
intervalTo :: a -> Interval a
intervalTo = Interval.to

-- | Emit a warning if the value at an address is zero.
warnEmptyTransaction :: (Member Log effs) => Value -> Address -> Eff effs ()
warnEmptyTransaction value addr =
    when (Value.isZero value)
        $ logWarn
        $ Text.unwords [
              "Attempting to collect transaction outputs from"
            , "'" <> Text.pack (show addr) <> "'" <> ","
            , "but there are no known outputs at that address."
            , "An empty transaction will be submitted."
            ]
