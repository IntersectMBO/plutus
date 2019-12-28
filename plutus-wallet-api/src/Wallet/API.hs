{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | The interface between the wallet and Plutus client code.
module Wallet.API(
    WalletAPI(..),
    WalletDiagnostics(..),
    MonadWallet,
    PubKey(..),
    createPaymentWithChange,
    signTxn,
    signTxnWithKey,
    createTxAndSubmit,
    signTxAndSubmit,
    signTxAndSubmit_,
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
    throwPrivateKeyNotFoundError,
    throwInsufficientFundsError,
    throwOtherError,
    ) where

import           Control.Lens              hiding (contains)
import           Control.Monad             (void, when)
import           Control.Monad.Error.Class (MonadError (..))
import           Data.Aeson                (FromJSON, ToJSON)
import qualified Data.ByteString.Lazy      as BSL
import           Data.Foldable             (fold)
import qualified Data.Map                  as Map
import           Data.Maybe                (fromMaybe, mapMaybe, maybeToList)
import qualified Data.Set                  as Set
import           Data.Text                 (Text)
import           IOTS                      (IotsType)

import qualified Data.Text                 as Text
import           Data.Text.Prettyprint.Doc hiding (width)
import           GHC.Generics              (Generic)
import           Ledger                    hiding (inputs, out, sign, to, value)
import           Ledger.AddressMap         (AddressMap)
import           Ledger.Index              (minFee)
import           Ledger.Interval           (Interval (..), after, always, before, contains, interval, isEmpty, member)
import qualified Ledger.Interval           as Interval
import qualified Ledger.Value              as Value

import           Prelude                   hiding (Ordering (..))

-- | An error thrown by wallet interactions.
data WalletAPIError =
    InsufficientFunds Text
    -- ^ There were insufficient funds to perform the desired operation.
    | PrivateKeyNotFound PubKey
    -- ^ The private key of this public key is not known to the wallet.
    | OtherError Text
    -- ^ Some other error occurred.
    deriving (Show, Eq, Ord, Generic, IotsType)

instance Pretty WalletAPIError where
    pretty = \case
        InsufficientFunds t ->
            "Insufficient funds:" <+> pretty t
        PrivateKeyNotFound pk ->
            "Private key not found:" <+> viaShow pk
        OtherError t ->
            "Other error:" <+> pretty t

instance FromJSON WalletAPIError
instance ToJSON WalletAPIError

type MonadWallet m = (WalletAPI m, WalletDiagnostics m)

-- | The ability to log messages and throw errors.
class MonadError WalletAPIError m => WalletDiagnostics m where
    -- | Write some information to the log.
    logMsg :: Text -> m ()

-- | Used by Plutus client to interact with wallet
class WalletAPI m where

    -- | Submit a transaction to the blockchain.
    submitTxn :: Tx -> m ()

    -- | Access the wallet's 'PublicKey'.
    ownPubKey :: m PubKey

    -- | Sign a message using the wallet's private key
    --   NOTE: In the future this won't be part of WalletAPI to allow the
    --   signing to be handled by a different process
    sign :: BSL.ByteString -> m Signature

    {- |
    Select enough inputs from the user's UTxOs to make a payment of the given value.
    Includes an output for any leftover funds, if there are any. Fails if we don't have enough funds.

    This can also be used iteratively, by passing the outputs from this function as its inputs, and
    a new value we want to spend. New inputs will be added to the input set to cover the new values,
    as required.
    -}
    updatePaymentWithChange :: Value -> (Set.Set TxIn, Maybe TxOut) -> m (Set.Set TxIn, Maybe TxOut)

    {- |
    The 'AddressMap' of all addresses currently watched by the wallet.
    -}
    watchedAddresses :: m AddressMap

    {- |
    Start watching an address.
    -}
    startWatching :: Address -> m ()

    {- |
    The current slot.
    -}
    slot :: m Slot

createPaymentWithChange :: WalletAPI m => Value -> m (Set.Set TxIn, Maybe TxOut)
createPaymentWithChange v = updatePaymentWithChange v (Set.empty, Nothing)

throwInsufficientFundsError :: MonadError WalletAPIError m => Text -> m a
throwInsufficientFundsError = throwError . InsufficientFunds

throwOtherError :: MonadError WalletAPIError m => Text -> m a
throwOtherError = throwError . OtherError

throwPrivateKeyNotFoundError :: MonadError WalletAPIError m => PubKey -> m a
throwPrivateKeyNotFoundError = throwError . PrivateKeyNotFound

-- | Sign the transaction with the private key of the given public
--   key. Fails if the wallet doesn't have the private key.
signTxnWithKey :: (WalletAPI m, MonadError WalletAPIError m) => Tx -> PubKey -> m Tx
signTxnWithKey tx pubK = do
    -- at the moment we only know a single private key: the one
    -- belonging to 'ownPubKey'.
    ownPubK <- ownPubKey
    if ownPubK == pubK
    then signTxn tx
    else throwPrivateKeyNotFoundError pubK

-- | Sign the transaction with the wallet's private key and add
--   the signature to the transaction's list of signatures.
--
--   NOTE: In the future this won't be part of WalletAPI to allow the
--   signing to be handled by a different process
signTxn   :: (WalletAPI m, Monad m) => Tx -> m Tx
signTxn tx = do
    pubK <- ownPubKey
    sig <- sign (getTxId $ txId tx)
    pure $ tx & signatures . at pubK ?~ sig

-- | Transfer some funds to a number of script addresses, returning the
-- transaction that was submitted.
payToScripts :: (Monad m, WalletAPI m) => SlotRange -> [(Address, Value, DataValue)] -> m Tx
payToScripts range ins = do
    let
        totalVal     = fold $ fmap (view _2) ins
        otherOutputs = fmap (\(addr, vl, ds) -> TxOut addr vl (PayToScript (dataValueHash ds))) ins
        datas        = fmap (\(_, _, d) -> d) ins
    (i, ownChange) <- createPaymentWithChange totalVal
    createTxAndSubmit range i (maybe otherOutputs (:otherOutputs) ownChange) datas

-- | Transfer some funds to a number of script addresses.
payToScripts_ :: (Monad m, WalletAPI m) => SlotRange -> [(Address, Value, DataValue)] -> m ()
payToScripts_ range = void . payToScripts range

-- | Transfer some funds to an address locked by a script, returning the
--   transaction that was submitted.
payToScript :: (Monad m, WalletAPI m) => SlotRange -> Address -> Value -> DataValue -> m Tx
payToScript range addr v ds = payToScripts range [(addr, v, ds)]

-- | Transfer some funds to an address locked by a script.
payToScript_ :: (Monad m, WalletAPI m) => SlotRange -> Address -> Value -> DataValue -> m ()
payToScript_ range addr v = void . payToScript range addr v

getScriptInputs
    :: AddressMap
    -> Validator
    -> RedeemerValue
    -> [(TxIn, Value)]
getScriptInputs = getScriptInputsFilter (\_ _ -> True)

getScriptInputsFilter
    :: (TxOutRef -> TxOutTx -> Bool)
    -> AddressMap
    -> Validator
    -> RedeemerValue
    -> [(TxIn, Value)]
getScriptInputsFilter flt am vls red =
    let utxo    = fromMaybe Map.empty $ am ^. at (scriptAddress vls)
        ourUtxo = Map.filterWithKey flt utxo
        mkIn :: TxOutRef -> DataValue -> TxIn
        mkIn ref = scriptTxIn ref vls red
        inputs =
            fmap (\(ref, dat, val) -> (mkIn ref dat, val)) $
            mapMaybe (\(ref, out) -> (ref,,txOutValue $ txOutTxOut out) <$> txOutTxData out) $
            Map.toList ourUtxo
    in inputs

spendScriptOutputs :: (Monad m, WalletAPI m) => Validator -> RedeemerValue -> m [(TxIn, Value)]
spendScriptOutputs = spendScriptOutputsFilter (\_ _ -> True)

-- | Take all known outputs at an 'Address' and spend them using the
--   validator and redeemer scripts.
spendScriptOutputsFilter :: (Monad m, WalletAPI m)
    => (TxOutRef -> TxOutTx -> Bool)
    -> Validator
    -> RedeemerValue
    -> m [(TxIn, Value)]
spendScriptOutputsFilter flt vls red = do
    am <- watchedAddresses
    pure $ getScriptInputsFilter flt am vls red

-- | Collect all unspent outputs from a pay to script address and transfer them
--   to a public key owned by us.
collectFromScript :: (WalletDiagnostics m, WalletAPI m) => SlotRange -> Validator -> RedeemerValue -> m ()
collectFromScript = collectFromScriptFilter (\_ _ -> True)

-- | Given the pay to script address of the 'Validator', collect from it
--   all the outputs that were produced by a specific transaction, using the
--   'RedeemerValue'.
collectFromScriptTxn ::
    (WalletAPI m, WalletDiagnostics m)
    => SlotRange
    -> Validator
    -> RedeemerValue
    -> TxId
    -> m ()
collectFromScriptTxn range vls red txid =
    let flt k _ = txid == Ledger.txOutRefId k in
    collectFromScriptFilter flt range vls red

-- | Given the pay to script address of the 'Validator', collect from it
--   all the outputs that match a predicate, using the 'RedeemerValue'.
collectFromScriptFilter ::
    (WalletAPI m, WalletDiagnostics m)
    => (TxOutRef -> TxOutTx -> Bool)
    -> SlotRange
    -> Validator
    -> RedeemerValue
    -> m ()
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
payToPublicKey :: (Monad m, WalletAPI m) => SlotRange -> Value -> PubKey -> m Tx
payToPublicKey range v pk = do
    (i, own) <- createPaymentWithChange v
    let other = pubKeyTxOut v pk
    createTxAndSubmit range i (other : maybeToList own) []

-- | Transfer some funds to an address locked by a public key.
payToPublicKey_ :: (Monad m, WalletAPI m) => SlotRange -> Value -> PubKey -> m ()
payToPublicKey_ r v = void . payToPublicKey r v

-- | Create a `TxOut` that pays to the public key owned by us.
ownPubKeyTxOut :: (Monad m, WalletAPI m) => Value -> m TxOut
ownPubKeyTxOut v = pubKeyTxOut v <$> ownPubKey

-- | Retrieve the unspent transaction outputs known to the wallet at an adresss.
outputsAt :: (Functor m, WalletAPI m) => Address -> m (Map.Map Ledger.TxOutRef TxOutTx)
outputsAt adr = fmap (\utxos -> fromMaybe Map.empty $ utxos ^. at adr) watchedAddresses

-- | Create a transaction, sign it with the wallet's private key, and submit it.
--   TODO: This is here to make the calculation of fees easier for old-style contracts
--         and should be removed when all contracts have been ported to the new API.
createTxAndSubmit ::
    (Monad m, WalletAPI m)
    => SlotRange
    -> Set.Set TxIn
    -> [TxOut]
    -> [DataValue]
    -> m Tx
createTxAndSubmit range ins outs datas = do
    let tx = Tx
            { txInputs = ins
            , txOutputs = outs
            , txForge = mempty
            , txFee = 0
            , txValidRange = range
            , txSignatures = Map.empty
            , txData = Map.fromList $ fmap (\ds -> (dataValueHash ds, ds)) datas
            }
    signTxAndSubmit $ tx { txFee = minFee tx }

-- | Add the wallet's signature to the transaction and submit it. Returns
--   the transaction with the wallet's signature.
signTxAndSubmit :: (Monad m, WalletAPI m) => Tx -> m Tx
signTxAndSubmit t = do
    tx' <- signTxn t
    submitTxn tx'
    pure tx'

-- | A version of 'signTxAndSubmit' that discards the result.
signTxAndSubmit_ :: (Monad m, WalletAPI m) => Tx -> m ()
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
warnEmptyTransaction :: (WalletDiagnostics m) => Value -> Address -> m ()
warnEmptyTransaction value addr =
    when (Value.isZero value)
        $ logMsg
        $ Text.unwords [
              "Attempting to collect transaction outputs from"
            , "'" <> Text.pack (show addr) <> "'" <> ","
            , "but there are no known outputs at that address."
            , "An empty transaction will be submitted."
            ]
