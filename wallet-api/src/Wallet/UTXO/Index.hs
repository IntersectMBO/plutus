{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
-- | An index of unspent transaction outputs, and some functions for validating
--   transactions using the UTXO index.
module Wallet.UTXO.Index(
    --  * Types for transaction validation based on UTXO index
    ValidationMonad,
    UtxoIndex(..),
    empty,
    insert,
    insertBlock,
    initialise,
    Validation,
    runValidation,
    lookupRef,
    lkpValue,
    lkpSigs,
    lkpTxOut,
    lkpOutputs,
    ValidationError(..),
    InOutMatch(..),
    -- * Actual validation
    validateTransaction
    ) where

import           Control.Monad.Except (MonadError (..), liftEither)
import           Control.Monad.Reader (MonadReader (..), ReaderT (..), ask)
import           Crypto.Hash          (Digest, SHA256)
import           Data.Foldable        (foldl', traverse_)
import qualified Data.Map             as Map
import           Data.Semigroup       (Semigroup, Sum (..))
import qualified Data.Set             as Set
import           GHC.Generics         (Generic)
import           Prelude              hiding (lookup)
import           Wallet.UTXO.Runtime  (PendingTx (..))
import qualified Wallet.UTXO.Runtime  as Runtime
import           Wallet.UTXO.Types    (Blockchain, DataScript, PubKey, Signature, Tx (..), TxIn (..), TxIn', TxOut (..),
                                       TxOut', TxOutRef', ValidationData (..), Value, lifted, updateUtxo, validValuesTx)
import qualified Wallet.UTXO.Types    as UTXO

-- | Context for validating transactions. We need access to the unspent
--   transaction outputs of the blockchain, and we can throw `ValidationError`s
type ValidationMonad m = (MonadReader UtxoIndex m, MonadError ValidationError m)

-- | The transactions of a blockchain indexed by hash
newtype UtxoIndex = UtxoIndex { getIndex :: Map.Map TxOutRef' (TxOut', [Signature]) }
    deriving (Eq, Ord, Show, Semigroup)

-- | An empty [[UtxoIndex]]
empty :: UtxoIndex
empty = UtxoIndex Map.empty

-- | Create an index of all transactions on the chain
initialise :: Blockchain -> UtxoIndex
initialise = UtxoIndex . UTXO.unspentOutputsAndSigs

-- | Add a transaction to the index
insert :: Tx -> UtxoIndex -> UtxoIndex
insert tx = UtxoIndex . updateUtxo tx . getIndex

-- | Add a block of transactions to the index
insertBlock :: [Tx] -> UtxoIndex -> UtxoIndex
insertBlock blck i = foldl' (flip insert) i blck

-- | Find an unspent transaction output by the `TxOutRef'` that spends it.
lookup :: TxOutRef' -> UtxoIndex -> Either ValidationError (TxOut', [Signature])
lookup i =
    maybe (Left $ TxOutRefNotFound i) Right . Map.lookup i . getIndex

-- | Reason why a transaction is invalid
data ValidationError =
    InOutTypeMismatch TxIn' TxOut'
    -- ^ A pay-to-pubkey output was consumed by a pay-to-script input or vice versa
    | TxOutRefNotFound TxOutRef'
    -- ^ The unspent transaction output consumed by a transaction input could not be found (either because it was already spent, or because there was no transaction with the given hash on the blockchain)
    | InvalidScriptHash DataScript
    -- ^ (for pay-to-script outputs) The validator script provided in the transaction input does not match the hash specified in the transaction output
    | InvalidSignature PubKey Signature
    -- ^ (for pay-to-pubkey outputs) The signature of the transaction input does not match the public key of the transaction output
    | ValueNotPreserved Value Value
    -- ^ The amount spent by the transaction differs from the amount consumed by it
    | NegativeValue Tx
    -- ^ The transaction produces an output with a negative value
    | ScriptFailure
    -- ^ (for pay-to-script outputs) Evaluation of the validator script failed
    deriving (Eq, Show, Generic)

newtype Validation a = Validation { _runValidation :: (ReaderT UtxoIndex (Either ValidationError)) a }
    deriving (Functor, Applicative, Monad, MonadReader UtxoIndex, MonadError ValidationError)

-- | Find an unspent transaction output by its reference. Assumes that the
--   output for this reference exists. If you want to handle the lookup error
--   you can use `runLookup`.
lookupRef :: ValidationMonad m => TxOutRef' -> m (TxOut', [Signature])
lookupRef t = liftEither  . lookup t =<< ask

-- | Run a `Validation` on a `UtxoIndex`
runValidation :: Validation a -> UtxoIndex -> Either ValidationError a
runValidation l = runReaderT (_runValidation l)

-- | Determine the unspent value that a [[TxOutRef']] refers to
lkpValue :: ValidationMonad m => TxOutRef' -> m Value
lkpValue = fmap txOutValue . lkpTxOut

-- | Determine the signatures of the transaction that [[TxOutRef']] refers to.
lkpSigs :: ValidationMonad m => TxOutRef' -> m [Signature]
lkpSigs o = snd <$> lookupRef o

-- | Determine the transaction output that a [[TxOutRef']] refers to
lkpTxOut :: ValidationMonad m => TxOutRef' -> m TxOut'
lkpTxOut o = fst <$> lookupRef o

-- | Validate a transaction in a `ValidationMonad` context.
--
--   This does the same as `Wallet.UTXO.Types.validTx`, but more efficiently as
--   it doesn't compute the UTXO of a blockchain from scratch.
--   It also gives a more precise error: `ValidationError` instead of `False`.
validateTransaction :: ValidationMonad m
    => UTXO.Height
    -> Tx
    -> m ()
validateTransaction h t =
    checkValuePreserved t >> checkPositiveValues t >> checkValidInputs h t

-- | Check if the inputs of the transaction consume outputs that
--   (a) exist and
--   (b) can be unlocked by the signatures or validator scripts of the inputs
checkValidInputs :: ValidationMonad m => UTXO.Height -> Tx -> m ()
checkValidInputs h tx = do
    matches <- lkpOutputs tx >>= traverse (uncurry matchInputOutput)
    vld     <- validationData h tx
    traverse_ (checkMatch vld) matches

-- | Match each input of the transaction with its output
lkpOutputs :: ValidationMonad m => Tx -> m [(TxIn', TxOut')]
lkpOutputs = traverse (\t -> traverse (lkpTxOut . txInRef) (t, t)) . Set.toList . txInputs

-- | Matching pair of transaction input and transaction output. The type
--   parameter is to allow the validation data to be inserted.
data InOutMatch =
    ScriptMatch UTXO.Validator UTXO.Redeemer DataScript (UTXO.Address (Digest SHA256))
    | PubKeyMatch PubKey Signature
    deriving (Eq, Ord, Show)

-- | Match a transaction input with the output that it consumes, ensuring that
--   both are of the same type (pubkey or pay-to-script)
matchInputOutput :: ValidationMonad m => TxIn' -> TxOut' -> m InOutMatch
matchInputOutput i txo = case (txInType i, txOutType txo) of
    (UTXO.ConsumeScriptAddress v r, UTXO.PayToScript d) ->
        pure $ ScriptMatch v r d (txOutAddress txo)
    (UTXO.ConsumePublicKeyAddress sig, UTXO.PayToPubKey pk) ->
        pure $ PubKeyMatch pk sig
    _ -> throwError $ InOutTypeMismatch i txo

-- | Check that a matching pair of transaction input and transaction output is
--   valid. If this is a pay-to-script output then the script hash needs to be
--   correct and script evaluation has to terminate successfully. If this is a
--   pay-to-pubkey output then the signature needs to match the public key that
--   locks it.
checkMatch :: ValidationMonad m => PendingTx () -> InOutMatch -> m ()
checkMatch v = \case
    ScriptMatch vl r d a
        | a /= UTXO.scriptAddress vl ->
                throwError $ InvalidScriptHash d
        | otherwise ->
            let v' = ValidationData
                    $ lifted
                    $ v { pendingTxOwnHash = Runtime.plcValidatorDigest (UTXO.getAddress a) }
            in
                if UTXO.runScript v' vl r d
                then pure ()
                else throwError ScriptFailure
    PubKeyMatch pk sig ->
        if sig `UTXO.signedBy` pk
        then pure ()
        else throwError $ InvalidSignature pk sig

-- | Check if the value produced by a transaction equals the value consumed by
--   it.
checkValuePreserved :: ValidationMonad m => Tx -> m ()
checkValuePreserved t = do
    inVal <- (txForge t +) <$> fmap (getSum . foldMap Sum) (traverse (lkpValue . txInRef) (Set.toList $ txInputs t))
    let outVal = txFee t + sum (map txOutValue (txOutputs t))
    if outVal == inVal
    then pure ()
    else throwError $ ValueNotPreserved inVal outVal

-- | Check if all values produced and consumed by a transaction are
--   non-negative.
checkPositiveValues :: ValidationMonad m => Tx -> m ()
checkPositiveValues t =
    if validValuesTx t
    then pure ()
    else throwError $ NegativeValue t

-- | Encode the current transaction and blockchain height
--   in PLC.
validationData :: ValidationMonad m => UTXO.Height -> Tx -> m (PendingTx ())
validationData h tx = rump <$> ins where
    ins = traverse mkIn $ Set.toList $ txInputs tx

    rump inputs = PendingTx
        { pendingTxInputs = inputs
        , pendingTxOutputs = mkOut <$> txOutputs tx
        , pendingTxForge = fromIntegral $ txForge tx
        , pendingTxFee = fromIntegral $ txFee tx
        , pendingTxBlockHeight = fromIntegral h
        , pendingTxSignatures = txSignatures tx
        , pendingTxOwnHash    = ()
        }

mkOut :: TxOut' -> Runtime.PendingTxOut
mkOut t = Runtime.PendingTxOut (fromIntegral $ txOutValue t) d tp where
    (d, tp) = case txOutType t of
        UTXO.PayToScript scrpt ->
            let
                dataScriptHash = Runtime.plcDataScriptHash scrpt
                validatorHash  = Runtime.plcValidatorDigest (UTXO.getAddress $ txOutAddress t)
            in
                (Just (validatorHash, dataScriptHash), Runtime.DataTxOut)
        UTXO.PayToPubKey pk -> (Nothing, Runtime.PubKeyTxOut pk)

mkIn :: ValidationMonad m => TxIn' -> m Runtime.PendingTxIn
mkIn i = Runtime.PendingTxIn <$> ref <*> pure red <*> vl where
    ref =
        let hash = Runtime.plcTxHash . UTXO.txOutRefId $ txInRef i
            idx  = UTXO.txOutRefIdx $ UTXO.txInRef i
        in
            Runtime.PendingTxOutRef hash idx <$> lkpSigs (UTXO.txInRef i)
    red = case txInType i of
        UTXO.ConsumeScriptAddress v r  ->
            let h = UTXO.getAddress $ UTXO.scriptAddress v in
            Just (Runtime.plcValidatorDigest h, Runtime.plcRedeemerHash r)
        UTXO.ConsumePublicKeyAddress _ ->
            Nothing
    vl = fromIntegral <$> valueOf i

valueOf :: ValidationMonad m => UTXO.TxIn' -> m Value
valueOf = lkpValue . txInRef
