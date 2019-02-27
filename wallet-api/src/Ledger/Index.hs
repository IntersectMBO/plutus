{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
-- | An index of unspent transaction outputs, and some functions for validating
--   transactions using the UTXO index.
module Ledger.Index(
    --  * Types for transaction validation based on UTXO index
    ValidationMonad,
    UtxoIndex(..),
    insert,
    insertBlock,
    initialise,
    Validation,
    runValidation,
    lkpValue,
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
import           Data.Aeson           (FromJSON, ToJSON)
import           Data.Foldable        (foldl', traverse_)
import qualified Data.Map             as Map
import           Data.Semigroup       (Semigroup)
import qualified Data.Set             as Set
import           GHC.Generics         (Generic)
import qualified Ledger.Interval      as Interval
import           Ledger.Types         (Blockchain, DataScript, PubKey, Signature, Slot (..), Tx (..), TxIn, TxInOf (..),
                                       TxOut, TxOutOf (..), TxOutRef, ValidationData (..), Value, lifted, updateUtxo,
                                       validValuesTx)
import qualified Ledger.Types         as Ledger
import           Ledger.Validation    (PendingTx (..))
import qualified Ledger.Validation    as Validation
import           Prelude              hiding (lookup)
import qualified Ledger.Value         as V
import qualified Ledger.Ada           as Ada

-- | Context for validating transactions. We need access to the unspent
--   transaction outputs of the blockchain, and we can throw `ValidationError`s
type ValidationMonad m = (MonadReader UtxoIndex m, MonadError ValidationError m)

-- | The transactions of a blockchain indexed by hash
newtype UtxoIndex = UtxoIndex { getIndex :: Map.Map TxOutRef TxOut }
    deriving (Eq, Ord, Show, Semigroup, Monoid)

-- | Create an index of all transactions on the chain
initialise :: Blockchain -> UtxoIndex
initialise = UtxoIndex . Ledger.unspentOutputs

-- | Add a transaction to the index
insert :: Tx -> UtxoIndex -> UtxoIndex
insert tx = UtxoIndex . updateUtxo tx . getIndex

-- | Add a block of transactions to the index
insertBlock :: [Tx] -> UtxoIndex -> UtxoIndex
insertBlock blck i = foldl' (flip insert) i blck

-- | Find an unspent transaction output by the `TxOutRef'` that spends it.
lookup :: TxOutRef -> UtxoIndex -> Either ValidationError TxOut
lookup i =
    maybe (Left $ TxOutRefNotFound i) Right . Map.lookup i . getIndex

-- | Reason why a transaction is invalid
data ValidationError =
    InOutTypeMismatch TxIn TxOut
    -- ^ A pay-to-pubkey output was consumed by a pay-to-script input or vice versa
    | TxOutRefNotFound TxOutRef
    -- ^ The unspent transaction output consumed by a transaction input could not be found (either because it was already spent, or because there was no transaction with the given hash on the blockchain)
    | InvalidScriptHash DataScript
    -- ^ (for pay-to-script outputs) The validator script provided in the transaction input does not match the hash specified in the transaction output
    | InvalidSignature PubKey Signature
    -- ^ (for pay-to-pubkey outputs) The signature of the transaction input does not match the public key of the transaction output
    | ValueNotPreserved Value Value
    -- ^ The amount spent by the transaction differs from the amount consumed by it
    | NegativeValue Tx
    -- ^ The transaction produces an output with a negative value
    | ScriptFailure [String]
    -- ^ (for pay-to-script outputs) Evaluation of the validator script failed
    | CurrentSlotOutOfRange Slot
    -- ^ The current slot is not covered by the transaction's validity slot range.
    deriving (Eq, Ord, Show, Generic)

instance FromJSON ValidationError
instance ToJSON ValidationError

newtype Validation a = Validation { _runValidation :: (ReaderT UtxoIndex (Either ValidationError)) a }
    deriving (Functor, Applicative, Monad, MonadReader UtxoIndex, MonadError ValidationError)

-- | Run a `Validation` on a `UtxoIndex`
runValidation :: Validation a -> UtxoIndex -> Either ValidationError a
runValidation l = runReaderT (_runValidation l)

-- | Determine the unspent value that a [[TxOutRef]] refers to
lkpValue :: ValidationMonad m => TxOutRef -> m Value
lkpValue = fmap txOutValue . lkpTxOut

-- | Find an unspent transaction output by its reference. Assumes that the
--   output for this reference exists. If you want to handle the lookup error
--   you can use `runLookup`.
--   Determine the transaction output that a [[TxOutRef']] refers to
lkpTxOut :: ValidationMonad m => TxOutRef -> m TxOut
lkpTxOut t = liftEither  . lookup t =<< ask

-- | Validate a transaction in a `ValidationMonad` context.
--
--   This does the same as `Ledger.Types.validTx`, but more efficiently as
--   it doesn't compute the UTXO of a blockchain from scratch.
--   It also gives a more precise error: `ValidationError` instead of `False`.
validateTransaction :: ValidationMonad m
    => Ledger.Slot
    -> Tx
    -> m UtxoIndex
validateTransaction h t = do
    _ <- checkSlotRange h t
    _ <- checkValuePreserved t
    _ <- checkPositiveValues t
    _ <- checkValidInputs t
    insert t <$> ask

-- | Check that a transaction can be validated in the given slot.
checkSlotRange :: ValidationMonad m => Ledger.Slot -> Tx -> m ()
checkSlotRange sl tx = 
    if $$(Interval.member) sl (txValidRange tx)
    then pure ()
    else throwError $ CurrentSlotOutOfRange sl

-- | Check if the inputs of the transaction consume outputs that
--   (a) exist and
--   (b) can be unlocked by the signatures or validator scripts of the inputs
checkValidInputs :: ValidationMonad m => Tx -> m ()
checkValidInputs tx = do
    matches <- lkpOutputs tx >>= traverse (uncurry matchInputOutput)
    vld     <- validationData tx
    traverse_ (checkMatch vld) matches

-- | Match each input of the transaction with its output
lkpOutputs :: ValidationMonad m => Tx -> m [(TxIn, TxOut)]
lkpOutputs = traverse (\t -> traverse (lkpTxOut . txInRef) (t, t)) . Set.toList . txInputs

-- | Matching pair of transaction input and transaction output.
data InOutMatch =
    ScriptMatch
        TxIn
        Ledger.ValidatorScript
        Ledger.RedeemerScript
        DataScript
        (Ledger.AddressOf (Digest SHA256))
    | PubKeyMatch PubKey Signature
    deriving (Eq, Ord, Show)

-- | Match a transaction input with the output that it consumes, ensuring that
--   both are of the same type (pubkey or pay-to-script)
matchInputOutput :: ValidationMonad m => TxIn -> TxOut -> m InOutMatch
matchInputOutput i txo = case (txInType i, txOutType txo) of
    (Ledger.ConsumeScriptAddress v r, Ledger.PayToScript d) ->
        pure $ ScriptMatch i v r d (txOutAddress txo)
    (Ledger.ConsumePublicKeyAddress sig, Ledger.PayToPubKey pk) ->
        pure $ PubKeyMatch pk sig
    _ -> throwError $ InOutTypeMismatch i txo

-- | Check that a matching pair of transaction input and transaction output is
--   valid. If this is a pay-to-script output then the script hash needs to be
--   correct and script evaluation has to terminate successfully. If this is a
--   pay-to-pubkey output then the signature needs to match the public key that
--   locks it.
checkMatch :: ValidationMonad m => PendingTx -> InOutMatch -> m ()
checkMatch v = \case
    ScriptMatch txin vl r d a
        | a /= Ledger.scriptAddress vl ->
                throwError $ InvalidScriptHash d
        | otherwise -> do
            pTxIn <- mkIn txin
            let v' = ValidationData
                    $ lifted
                    $ v { pendingTxIn = pTxIn }
                (logOut, success) = Ledger.runScript v' vl r d
            if success
            then pure ()
            else throwError $ ScriptFailure logOut
    PubKeyMatch pk sig ->
        if sig `Ledger.signedBy` pk
        then pure ()
        else throwError $ InvalidSignature pk sig

-- | Check if the value produced by a transaction equals the value consumed by
--   it.
checkValuePreserved :: ValidationMonad m => Tx -> m ()
checkValuePreserved t = do
    let sumVal = foldl' V.plus V.zero
    inVal <- V.plus (txForge t) <$> fmap sumVal (traverse (lkpValue . txInRef) (Set.toList $ txInputs t))
    let outVal = V.plus (Ada.toValue $ txFee t) (sumVal (map txOutValue (txOutputs t)))
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

-- | Encode the current transaction and slot in PLC.
validationData :: ValidationMonad m => Tx -> m PendingTx
validationData tx = rump <$> ins where
    ins = traverse mkIn $ Set.toList $ txInputs tx

    rump inputs = PendingTx
        { pendingTxInputs = inputs
        , pendingTxOutputs = mkOut <$> txOutputs tx
        , pendingTxForge = txForge tx
        , pendingTxFee = txFee tx
        , pendingTxIn = head inputs -- this is changed accordingly in `checkMatch` during validation
        , pendingTxValidRange = txValidRange tx
        }

mkOut :: TxOut -> Validation.PendingTxOut
mkOut t = Validation.PendingTxOut (txOutValue t) d tp where
    (d, tp) = case txOutType t of
        Ledger.PayToScript scrpt ->
            let
                dataScriptHash = Validation.plcDataScriptHash scrpt
                validatorHash  = Validation.plcValidatorDigest (Ledger.getAddress $ txOutAddress t)
            in
                (Just (validatorHash, dataScriptHash), Validation.DataTxOut)
        Ledger.PayToPubKey pk -> (Nothing, Validation.PubKeyTxOut pk)

mkIn :: ValidationMonad m => TxIn -> m Validation.PendingTxIn
mkIn i = Validation.PendingTxIn <$> pure ref <*> pure red <*> vl where
    ref =
        let hash = Validation.plcTxHash . Ledger.txOutRefId $ txInRef i
            idx  = Ledger.txOutRefIdx $ Ledger.txInRef i
        in
            Validation.PendingTxOutRef hash idx
    red = case txInType i of
        Ledger.ConsumeScriptAddress v r  ->
            let h = Ledger.getAddress $ Ledger.scriptAddress v in
            Left (Validation.plcValidatorDigest h, Validation.plcRedeemerHash r)
        Ledger.ConsumePublicKeyAddress sig ->
            Right sig
    vl = valueOf i

valueOf :: ValidationMonad m => Ledger.TxIn -> m Value
valueOf = lkpValue . txInRef
