{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
    minFee,
    -- * Actual validation
    validateTransaction
    ) where

import           Prelude                          hiding (lookup)


import           Control.Lens                     ((^.))
import           Control.Monad
import           Control.Monad.Except             (MonadError (..), runExcept)
import           Control.Monad.Reader             (MonadReader (..), ReaderT (..), ask)
import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Foldable                    (asum, fold, foldl', traverse_)
import qualified Data.Map                         as Map
import           Data.Semigroup                   (Semigroup)
import qualified Data.Set                         as Set
import           Data.Text.Prettyprint.Doc        (Pretty)
import           Data.Text.Prettyprint.Doc.Extras (PrettyShow (..))
import           GHC.Generics                     (Generic)
import           Language.PlutusTx                (toData)
import qualified Language.PlutusTx.Numeric        as P
import qualified Ledger.Ada                       as Ada
import           Ledger.Address
import           Ledger.Blockchain
import           Ledger.Crypto
import qualified Ledger.Interval                  as Interval
import           Ledger.Scripts
import qualified Ledger.Scripts                   as Scripts
import qualified Ledger.Slot                      as Slot
import           Ledger.Tx
import           Ledger.TxId
import           Ledger.Validation                (PendingTx' (..))
import qualified Ledger.Validation                as Validation
import qualified Ledger.Value                     as V

-- | Context for validating transactions. We need access to the unspent
--   transaction outputs of the blockchain, and we can throw 'ValidationError's.
type ValidationMonad m = (MonadReader UtxoIndex m, MonadError ValidationError m)

-- | The UTxOs of a blockchain indexed by their references.
newtype UtxoIndex = UtxoIndex { getIndex :: Map.Map TxOutRef TxOut }
    deriving (Show, Semigroup, Monoid)
    deriving newtype (Eq)

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
    Just t  -> pure t
    Nothing -> throwError $ TxOutRefNotFound i

-- | A reason why a transaction is invalid.
data ValidationError =
    InOutTypeMismatch TxIn TxOut
    -- ^ A pay-to-pubkey output was consumed by a pay-to-script input or vice versa, or the 'TxIn' refers to a different public key than the 'TxOut'.
    | TxOutRefNotFound TxOutRef
    -- ^ The transaction output consumed by a transaction input could not be found (either because it was already spent, or because
    -- there was no transaction with the given hash on the blockchain).
    | InvalidScriptHash Validator ValidatorHash
    -- ^ For pay-to-script outputs: the validator script provided in the transaction input does not match the hash specified in the transaction output.
    | InvalidDataHash DataValue DataValueHash
    -- ^ For pay-to-script outputs: the data value provided in the transaction input does not match the hash specified in the transaction output.
    | InvalidSignature PubKey Signature
    -- ^ For pay-to-pubkey outputs: the signature of the transaction input does not match the public key of the transaction output.
    | ValueNotPreserved V.Value V.Value
    -- ^ The amount spent by the transaction differs from the amount consumed by it.
    | NegativeValue Tx
    -- ^ The transaction produces an output with a negative value.
    | NonAdaFees Tx
    -- ^ The fee is not denominated entirely in Ada.
    | ScriptFailure ScriptError
    -- ^ For pay-to-script outputs: evaluation of the validator script failed.
    | CurrentSlotOutOfRange Slot.Slot
    -- ^ The current slot is not covered by the transaction's validity slot range.
    | SignatureMissing PubKeyHash
    -- ^ The transaction is missing a signature
    | ForgeWithoutScript Scripts.MonetaryPolicyHash
    -- ^ The transaction attempts to forge value of a currency without running
    --   the currency's monetary policy.
    | TransactionFeeTooLow V.Value V.Value
    -- ^ The transaction fee is lower than the minimum acceptable fee.
    deriving (Eq, Show, Generic)

instance FromJSON ValidationError
instance ToJSON ValidationError
deriving via (PrettyShow ValidationError) instance Pretty ValidationError

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
    _ <- checkFeeIsAda t

    -- see note [Forging of Ada]
    emptyUtxoSet <- reader (Map.null . getIndex)
    unless emptyUtxoSet (checkForgingScripts t)
    unless emptyUtxoSet (checkForgingAuthorised t)
    unless emptyUtxoSet (checkTransactionFee t)

    _ <- checkValidInputs t
    insert t <$> ask

-- | Check that a transaction can be validated in the given slot.
checkSlotRange :: ValidationMonad m => Slot.Slot -> Tx -> m ()
checkSlotRange sl tx =
    if Interval.member sl (txValidRange tx)
    then pure ()
    else throwError $ CurrentSlotOutOfRange sl

-- | Check if the inputs of the transaction consume outputs that exist, and
--   can be unlocked by the signatures or validator scripts of the inputs.
checkValidInputs :: ValidationMonad m => Tx -> m ()
checkValidInputs tx = do
    let tid = txId tx
        sigs = tx ^. signatures
    matches <- lkpOutputs tx >>= traverse (uncurry (matchInputOutput tid sigs))
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
        forgedCurrencies = V.symbols (txForge tx)

        mpsScriptHashes = Scripts.MonetaryPolicyHash . V.unCurrencySymbol <$> forgedCurrencies

        lockingScripts = monetaryPolicyHash <$> Set.toList (txForgeScripts tx)

        forgedWithoutScript = filter (\c -> c `notElem` lockingScripts) mpsScriptHashes
    in
        traverse_ (throwError . ForgeWithoutScript) forgedWithoutScript

checkForgingScripts :: forall m . ValidationMonad m => Tx -> m ()
checkForgingScripts tx = do
    ptx <- validationData tx
    let mpss = Set.toList (txForgeScripts tx)
        mkVd :: Integer -> Validation.PendingTxMPS
        mkVd i = ptx { pendingTxItem = monetaryPolicyHash $ mpss !! fromIntegral i }
    forM_ (mpss `zip` (mkVd <$> [0..])) $ \(vl, ptx') ->
        let vd = ValidationData $ toData ptx'
        in case runExcept $ runMonetaryPolicyScript Typecheck vd vl of
            Left e  -> throwError $ ScriptFailure e
            Right _ -> pure ()

-- | A matching pair of transaction input and transaction output, ensuring that they are of matching types also.
data InOutMatch =
    ScriptMatch
        TxIn
        Validator
        RedeemerValue
        DataValue
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
matchInputOutput txid mp i txo = case (txInType i, txOutType txo, txOutAddress txo) of
    (ConsumeScriptAddress v r d, PayToScript dh, ScriptAddress vh) -> do
        unless (dataValueHash d == dh) $ throwError $ InvalidDataHash d dh
        unless (validatorHash v == vh) $ throwError $ InvalidScriptHash v vh

        pure $ ScriptMatch i v r d
    (ConsumePublicKeyAddress, PayToPubKey, PubKeyAddress pkh) ->
        let sigMatches = (flip fmap) (Map.toList mp) $ \(pk,sig) ->
                if pubKeyHash pk == pkh
                then Just (PubKeyMatch txid pk sig)
                else Nothing
        in case asum sigMatches of
            Just m  -> pure m
            Nothing -> throwError $ SignatureMissing pkh
    _ -> throwError $ InOutTypeMismatch i txo

-- | Check that a matching pair of transaction input and transaction output is
--   valid. If this is a pay-to-script output then the script hash needs to be
--   correct and script evaluation has to terminate successfully. If this is a
--   pay-to-pubkey output then the signature needs to match the public key that
--   locks it.
checkMatch :: ValidationMonad m => PendingTxNoIn -> InOutMatch -> m ()
checkMatch pendingTx = \case
    ScriptMatch txin vl r d -> do
        pTxIn <- pendingTxInScript (txInRef txin) vl r d
        let
            ptx' = pendingTx { pendingTxItem = pTxIn }
            vd = ValidationData (toData ptx')
        case runExcept $ runScript Typecheck vd vl d r of
            Left e  -> throwError $ ScriptFailure e
            Right _ -> pure ()
    PubKeyMatch msg pk sig -> unless (signedBy sig pk msg) $ throwError $ InvalidSignature pk sig

-- | Check if the value produced by a transaction equals the value consumed by it.
checkValuePreserved :: ValidationMonad m => Tx -> m ()
checkValuePreserved t = do
    inVal <- (P.+) (txForge t) <$> fmap fold (traverse (lkpValue . txInRef) (Set.toList $ txInputs t))
    let outVal = txFee t P.+ foldMap txOutValue (txOutputs t)
    if outVal == inVal
    then pure ()
    else throwError $ ValueNotPreserved inVal outVal

-- | Check if all values produced and consumed by a transaction are non-negative.
checkPositiveValues :: ValidationMonad m => Tx -> m ()
checkPositiveValues t =
    if validValuesTx t
    then pure ()
    else throwError $ NegativeValue t

-- | Check if the fees are paid exclusively in Ada.
checkFeeIsAda :: ValidationMonad m => Tx -> m ()
checkFeeIsAda t =
    if (Ada.toValue $ Ada.fromValue $ txFee t) == txFee t
    then pure ()
    else throwError $ NonAdaFees t

-- | Minimum transaction fee.
minFee :: Tx -> V.Value
minFee = const mempty

-- | Check that transaction fee is bigger than the minimum fee.
--   Skip the check on the first transaction (no inputs).
checkTransactionFee :: ValidationMonad m => Tx -> m ()
checkTransactionFee tx =
    if minFee tx `V.leq` txFee tx
    then pure ()
    else throwError $ TransactionFeeTooLow (txFee tx) (minFee tx)

-- | A 'PendingTx' without a current transaction input in 'pendingTxItem'
type PendingTxNoIn = Validation.PendingTx' ()

-- | Create the data about the transaction which will be passed to a validator script.
validationData :: ValidationMonad m => Tx -> m PendingTxNoIn
validationData tx = do
    txins <- traverse mkIn $ Set.toList $ txInputs tx
    let ptx = PendingTx
            { pendingTxInputs = txins
            , pendingTxOutputs = mkOut <$> txOutputs tx
            , pendingTxForge = txForge tx
            , pendingTxFee = txFee tx
            , pendingTxItem = () -- this is changed accordingly in `checkMatch` during validation
            , pendingTxValidRange = txValidRange tx
            , pendingTxForgeScripts = monetaryPolicyHash <$> Set.toList (tx ^. forgeScripts)
            , pendingTxSignatories = fmap pubKeyHash $ Map.keys (tx ^. signatures)
            , pendingTxData = Map.toList (tx ^. dataWitnesses)
            , pendingTxId = txId tx
            }
    pure ptx

-- | Create the data about a transaction output which will be passed to a validator script.
mkOut :: TxOut -> Validation.PendingTxOut
mkOut t = Validation.PendingTxOut (txOutValue t) tp where
    tp = case (txOutType t, txOutAddress t) of
        (PayToScript dh, ScriptAddress vh) -> Validation.ScriptTxOut vh dh
        (PayToPubKey, PubKeyAddress pkh)   -> Validation.PubKeyTxOut pkh
        _                                  -> error "nope"

pendingTxInScript
    :: ValidationMonad m
    => TxOutRef
    -> Validator
    -> RedeemerValue
    -> DataValue
    -> m Validation.PendingTxInScript
pendingTxInScript outRef val red dat = txInFromRef outRef witness where
        witness = (Scripts.validatorHash val, Scripts.redeemerHash red, Scripts.dataValueHash dat)

txInFromRef
    :: ValidationMonad m
    => TxOutRef
    -> a
    -> m (Validation.PendingTxIn' a)
txInFromRef outRef witness = Validation.PendingTxIn ref witness <$> vl where
    vl = lkpValue outRef
    ref =
        let tid = txOutRefId outRef
            idx  = txOutRefIdx outRef
        in Validation.PendingTxOutRef tid idx

pendingTxInPubkey
    :: ValidationMonad m
    => TxOutRef
    -> m Validation.PendingTxIn
pendingTxInPubkey outRef = txInFromRef outRef Nothing

-- | Create the data about a transaction input which will be passed to a validator script.
mkIn :: ValidationMonad m => TxIn -> m Validation.PendingTxIn
mkIn TxIn{txInRef, txInType} = case txInType of
    ConsumeScriptAddress v r d ->
        Validation.toLedgerTxIn <$> pendingTxInScript txInRef v r d
    ConsumePublicKeyAddress -> pendingTxInPubkey txInRef
