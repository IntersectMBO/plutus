{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
-- | An index of unspent transaction outputs, and some functions for validating
--   transactions using the index.
module Ledger.Index(
    -- * Types for transaction validation based on UTXO index
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

import           Control.Lens         ((^.), at)
import           Control.Monad.Except (MonadError (..))
import           Control.Monad.Reader (MonadReader (..), ReaderT (..), ask)
import           Control.Monad
import           Crypto.Hash          (Digest, SHA256)
import           Data.Aeson           (FromJSON, ToJSON)
import           Data.Foldable        (foldl', traverse_)
import qualified Data.Map             as Map
import           Data.Semigroup       (Semigroup)
import qualified Data.Set             as Set
import           GHC.Generics         (Generic)
import qualified Language.PlutusCore  as PLC
import qualified Ledger.Slot          as Slot
import           Ledger.Crypto
import           Ledger.Blockchain
import           Ledger.Scripts
import           Ledger.Tx
import           Ledger.TxId
import           Ledger.Validation    (PendingTx (..))
import qualified Ledger.Validation    as Validation
import           Prelude              hiding (lookup)
import qualified Ledger.Value         as V
import qualified Ledger.Ada           as Ada

-- | Context for validating transactions. We need access to the unspent
--   transaction outputs of the blockchain, and we can throw 'ValidationError's.
type ValidationMonad m = (MonadReader UtxoIndex m, MonadError ValidationError m)

-- | The UTxOs of a blockchain indexed by their references.
newtype UtxoIndex = UtxoIndex { getIndex :: Map.Map TxOutRef TxOut }
    deriving (Eq, Ord, Show, Semigroup, Monoid)

-- | Create an index of all UTxOs on the chain.
initialise :: Blockchain -> UtxoIndex
initialise = UtxoIndex . unspentOutputs

-- | Update the index for the addition of a transaction.
insert :: Tx -> UtxoIndex -> UtxoIndex
insert tx = UtxoIndex . updateUtxo tx . getIndex

-- | Update the index for the addition of a block.
insertBlock :: [Tx] -> UtxoIndex -> UtxoIndex
insertBlock blck i = foldl' (flip insert) i blck

-- | Find an unspent transaction output by the 'TxOutRef' that spends it.
lookup :: MonadError ValidationError m => TxOutRef -> UtxoIndex -> m TxOut
lookup i index = case Map.lookup i $ getIndex index of
    Just t -> pure t
    Nothing -> throwError $ TxOutRefNotFound i

-- | A reason why a transaction is invalid.
data ValidationError =
    InOutTypeMismatch TxIn TxOut
    -- ^ A pay-to-pubkey output was consumed by a pay-to-script input or vice versa, or the 'TxIn' refers to a different public key than the 'TxOut'.
    | TxOutRefNotFound TxOutRef
    -- ^ The transaction output consumed by a transaction input could not be found (either because it was already spent, or because
    -- there was no transaction with the given hash on the blockchain).
    | InvalidScriptHash DataScript
    -- ^ For pay-to-script outputs: the validator script provided in the transaction input does not match the hash specified in the transaction output.
    | InvalidSignature PubKey Signature
    -- ^ For pay-to-pubkey outputs: the signature of the transaction input does not match the public key of the transaction output.
    | ValueNotPreserved V.Value V.Value
    -- ^ The amount spent by the transaction differs from the amount consumed by it.
    | NegativeValue Tx
    -- ^ The transaction produces an output with a negative value.
    | ScriptFailure [String]
    -- ^ For pay-to-script outputs: evaluation of the validator script failed.
    | CurrentSlotOutOfRange Slot.Slot
    -- ^ The current slot is not covered by the transaction's validity slot range.
    | SignatureMissing PubKey
    -- ^ The transaction is missing a signature
    | ForgeWithoutScript Validation.ValidatorHash
    -- ^ The transaction attempts to forge value of a currency without spending
    --   a script output from the address of the currency's monetary policy.
    deriving (Eq, Show, Generic)

instance FromJSON ValidationError
instance ToJSON ValidationError

-- | A monad for running transaction validation inside, which is an instance of 'ValidationMonad'.
newtype Validation a = Validation { _runValidation :: (ReaderT UtxoIndex (Either ValidationError)) a }
    deriving (Functor, Applicative, Monad, MonadReader UtxoIndex, MonadError ValidationError)

-- | Run a 'Validation' on a 'UtxoIndex'.
runValidation :: Validation a -> UtxoIndex -> Either ValidationError a
runValidation l = runReaderT (_runValidation l)

-- | Determine the unspent value that a ''TxOutRef' refers to.
lkpValue :: ValidationMonad m => TxOutRef -> m V.Value
lkpValue = fmap txOutValue . lkpTxOut

-- | Find an unspent transaction output by its reference. Assumes that the
--   output for this reference exists. If you want to handle the lookup error
--   you can use 'runLookup'.
lkpTxOut :: ValidationMonad m => TxOutRef -> m TxOut
lkpTxOut t = lookup t =<< ask

-- | Validate a transaction in a 'ValidationMonad' context.
validateTransaction :: ValidationMonad m
    => Slot.Slot
    -> Tx
    -> m UtxoIndex
validateTransaction h t = do
    _ <- checkSlotRange h t
    _ <- checkValuePreserved t
    _ <- checkPositiveValues t

    -- see note [Forging of Ada]
    emptyUtxoSet <- reader (Map.null . getIndex)
    _ <- unless emptyUtxoSet (checkForgingAuthorised t)

    _ <- checkValidInputs t
    insert t <$> ask

-- | Check that a transaction can be validated in the given slot.
checkSlotRange :: ValidationMonad m => Slot.Slot -> Tx -> m ()
checkSlotRange sl tx =
    if $$(Slot.member) sl (txValidRange tx)
    then pure ()
    else throwError $ CurrentSlotOutOfRange sl

-- | Check if the inputs of the transaction consume outputs that exist, and
--   can be unlocked by the signatures or validator scripts of the inputs.
checkValidInputs :: ValidationMonad m => Tx -> m ()
checkValidInputs tx = do
    let txId = hashTx tx
        sigs = tx ^. signatures
    matches <- lkpOutputs tx >>= traverse (uncurry (matchInputOutput txId sigs))
    vld     <- validationData tx
    traverse_ (checkMatch vld) matches

-- | Match each input of the transaction with the output that it spends.
lkpOutputs :: ValidationMonad m => Tx -> m [(TxIn, TxOut)]
lkpOutputs = traverse (\t -> traverse (lkpTxOut . txInRef) (t, t)) . Set.toList . txInputs

{- note [Forging of Ada]

'checkForgingAuthorised' will never allow a transaction that forges Ada.
Ada's currency symbol is the empty bytestring, and it can never be matched by a
validator script whose hash is its symbol.

Therefore 'checkForgingAuthorised' should not be applied to the first transaction in
the blockchain.

-}

-- | Check whether each currency forged by the transaction is matched by
--   a corresponding monetary policy script (in the form of a pay-to-script
--   output of the currency's address).
--
checkForgingAuthorised :: ValidationMonad m => Tx -> m ()
checkForgingAuthorised tx =
    let
        forgedCurrencies =
            V.unCurrencySymbol <$> V.symbols (txForge tx)

        spendsOutput i =
            let spentAddresses = Set.map inAddress (txInputs tx) in
            Set.member i spentAddresses

        forgedWithoutScript = filter (not . spendsOutput) forgedCurrencies

    in
        traverse_ (throwError . ForgeWithoutScript . Validation.ValidatorHash) forgedWithoutScript

-- | A matching pair of transaction input and transaction output, ensuring that they are of matching types also.
data InOutMatch =
    ScriptMatch
        TxIn
        ValidatorScript
        RedeemerScript
        DataScript
        (AddressOf (Digest SHA256))
    | PubKeyMatch TxId PubKey Signature
    deriving (Eq, Ord, Show)

-- | Match a transaction input with the output that it consumes, ensuring that
--   both are of the same type (pubkey or pay-to-script).
matchInputOutput :: ValidationMonad m
    => TxId
    -- ^ Hash of the transaction that is being verified
    -> Map.Map PubKey Signature
    -- ^ Signatures provided with the transaction
    -> TxIn
    -- ^ Input that allegedly spends the output
    -> TxOut
    -- ^ The unspent transaction output we are trying to unlock
    -> m InOutMatch
matchInputOutput txid mp i txo = case (txInType i, txOutType txo) of
    (ConsumeScriptAddress v r, PayToScript d) ->
        pure $ ScriptMatch i v r d (txOutAddress txo)
    (ConsumePublicKeyAddress pk', PayToPubKey pk)
        | pk == pk' -> case mp ^. at pk' of
                        Nothing -> throwError (SignatureMissing pk')
                        Just sig -> pure (PubKeyMatch txid pk sig)
    _ -> throwError $ InOutTypeMismatch i txo

-- | Check that a matching pair of transaction input and transaction output is
--   valid. If this is a pay-to-script output then the script hash needs to be
--   correct and script evaluation has to terminate successfully. If this is a
--   pay-to-pubkey output then the signature needs to match the public key that
--   locks it.
checkMatch :: ValidationMonad m => PendingTx -> InOutMatch -> m ()
checkMatch v = \case
    ScriptMatch txin vl r d a
        | a /= scriptAddress vl ->
                throwError $ InvalidScriptHash d
        | otherwise -> do
            pTxIn <- mkIn txin
            let v' = ValidationData
                    $ PLC.runQuote
                    $ normalizeScript
                    $ lifted
                    $ v { pendingTxIn = pTxIn }
                (logOut, success) = runScript v' vl d r
            if success
            then pure ()
            else throwError $ ScriptFailure logOut
    PubKeyMatch msg pk sig ->
        if signedBy sig pk msg
        then pure ()
        else throwError $ InvalidSignature pk sig

-- | Check if the value produced by a transaction equals the value consumed by it.
checkValuePreserved :: ValidationMonad m => Tx -> m ()
checkValuePreserved t = do
    let sumVal = foldl' V.plus V.zero
    inVal <- V.plus (txForge t) <$> fmap sumVal (traverse (lkpValue . txInRef) (Set.toList $ txInputs t))
    let outVal = V.plus (Ada.toValue $ txFee t) (sumVal (map txOutValue (txOutputs t)))
    if outVal == inVal
    then pure ()
    else throwError $ ValueNotPreserved inVal outVal

-- | Check if all values produced and consumed by a transaction are non-negative.
checkPositiveValues :: ValidationMonad m => Tx -> m ()
checkPositiveValues t =
    if validValuesTx t
    then pure ()
    else throwError $ NegativeValue t

-- | Create the data about the transaction which will be passed to a validator script.
validationData :: ValidationMonad m => Tx -> m PendingTx
validationData tx = rump <$> ins where
    ins = traverse mkIn $ Set.toList $ txInputs tx
    txHash = Validation.plcTxHash $ hashTx tx

    rump txins = PendingTx
        { pendingTxInputs = txins
        , pendingTxOutputs = mkOut <$> txOutputs tx
        , pendingTxForge = txForge tx
        , pendingTxFee = txFee tx
        , pendingTxIn = head txins -- this is changed accordingly in `checkMatch` during validation
        , pendingTxValidRange = txValidRange tx
        , pendingTxSignatures = Map.toList (tx ^. signatures)
        , pendingTxHash = txHash
        }

-- | Create the data about a transaction output which will be passed to a validator script.
mkOut :: TxOut -> Validation.PendingTxOut
mkOut t = Validation.PendingTxOut (txOutValue t) d tp where
    (d, tp) = case txOutType t of
        PayToScript scrpt ->
            let
                dataScriptHash = Validation.plcDataScriptHash scrpt
                validatorHash  = Validation.plcValidatorDigest (getAddress $ txOutAddress t)
            in
                (Just (validatorHash, dataScriptHash), Validation.DataTxOut)
        PayToPubKey pk -> (Nothing, Validation.PubKeyTxOut pk)

-- | Create the data about a transaction input which will be passed to a validator script.
mkIn :: ValidationMonad m => TxIn -> m Validation.PendingTxIn
mkIn i = Validation.PendingTxIn <$> pure ref <*> pure red <*> vl where
    ref =
        let hash = Validation.plcTxHash . txOutRefId $ txInRef i
            idx  = txOutRefIdx $ txInRef i
        in
            Validation.PendingTxOutRef hash idx
    red = case txInType i of
        ConsumeScriptAddress v r  ->
            let h = getAddress $ scriptAddress v in
            Just (Validation.plcValidatorDigest h, Validation.plcRedeemerHash r)
        ConsumePublicKeyAddress _ ->
            Nothing
    vl = valueOf i

-- | Get the 'Value' attached to a transaction input.
valueOf :: ValidationMonad m => TxIn -> m V.Value
valueOf = lkpValue . txInRef
