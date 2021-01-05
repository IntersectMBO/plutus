{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DeriveAnyClass      #-}
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


import           Codec.Serialise                  (Serialise)
import           Control.DeepSeq                  (NFData)
import           Control.Lens                     (itraverse, view, (^.))
import           Control.Monad
import           Control.Monad.Except             (MonadError (..), runExcept)
import           Control.Monad.Reader             (MonadReader (..), ReaderT (..), ask)
import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Foldable                    (asum, fold, foldl', traverse_)
import qualified Data.Map                         as Map
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
import           Ledger.Validation                (PolicyCtx (..), TxInfo (..), ValidatorCtx (..))
import qualified Ledger.Validation                as Validation
import qualified Ledger.Value                     as V

-- | Context for validating transactions. We need access to the unspent
--   transaction outputs of the blockchain, and we can throw 'ValidationError's.
type ValidationMonad m = (MonadReader UtxoIndex m, MonadError ValidationError m)

-- | The UTxOs of a blockchain indexed by their references.
newtype UtxoIndex = UtxoIndex { getIndex :: Map.Map TxOutRef TxOut }
    deriving stock (Show, Generic)
    deriving newtype (Eq, Semigroup, Monoid, Serialise)
    deriving anyclass (FromJSON, ToJSON, NFData)

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
    | InvalidDatumHash Datum DatumHash
    -- ^ For pay-to-script outputs: the datum provided in the transaction input does not match the hash specified in the transaction output.
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
    deriving newtype (Functor, Applicative, Monad, MonadReader UtxoIndex, MonadError ValidationError)

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
    outs <- lkpOutputs tx
    matches <- itraverse (\ix (txin, txout) -> matchInputOutput tid sigs ix txin txout) outs
    vld     <- mkTxInfo tx
    traverse_ (checkMatch vld) matches

-- | Match each input of the transaction with the output that it spends.
lkpOutputs :: ValidationMonad m => Tx -> m [(TxIn, TxOut)]
lkpOutputs = traverse (\t -> traverse (lkpTxOut . txInRef) (t, t)) . Set.toList . view inputs

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
    txinfo <- mkTxInfo tx
    let mpss = Set.toList (txForgeScripts tx)
        mkVd :: Integer -> PolicyCtx
        mkVd i = PolicyCtx { policyCtxPolicy = monetaryPolicyHash $ mpss !! fromIntegral i, policyCtxTxInfo = txinfo }
    forM_ (mpss `zip` (mkVd <$> [0..])) $ \(vl, ptx') ->
        let vd = Context $ toData ptx'
        in case runExcept $ runMonetaryPolicyScript vd vl of
            Left e  -> throwError $ ScriptFailure e
            Right _ -> pure ()

-- | A matching pair of transaction input and transaction output, ensuring that they are of matching types also.
data InOutMatch =
    ScriptMatch
        Integer
        Validator
        Redeemer
        Datum
    | PubKeyMatch TxId PubKey Signature
    deriving (Eq, Ord, Show)

-- | Match a transaction input with the output that it consumes, ensuring that
--   both are of the same type (pubkey or pay-to-script).
matchInputOutput :: ValidationMonad m
    => TxId
    -- ^ Hash of the transaction that is being verified
    -> Map.Map PubKey Signature
    -- ^ Signatures provided with the transaction
    -> Int
    -- ^ Index of the input
    -> TxIn
    -- ^ Input that allegedly spends the output
    -> TxOut
    -- ^ The unspent transaction output we are trying to unlock
    -> m InOutMatch
matchInputOutput txid mp ix txin txo = case (txInType txin, txOutType txo, txOutAddress txo) of
    (ConsumeScriptAddress v r d, PayToScript dh, ScriptAddress vh) -> do
        unless (datumHash d == dh) $ throwError $ InvalidDatumHash d dh
        unless (validatorHash v == vh) $ throwError $ InvalidScriptHash v vh

        pure $ ScriptMatch (fromIntegral ix) v r d
    (ConsumePublicKeyAddress, PayToPubKey, PubKeyAddress pkh) ->
        let sigMatches = flip fmap (Map.toList mp) $ \(pk,sig) ->
                if pubKeyHash pk == pkh
                then Just (PubKeyMatch txid pk sig)
                else Nothing
        in case asum sigMatches of
            Just m  -> pure m
            Nothing -> throwError $ SignatureMissing pkh
    _ -> throwError $ InOutTypeMismatch txin txo

-- | Check that a matching pair of transaction input and transaction output is
--   valid. If this is a pay-to-script output then the script hash needs to be
--   correct and script evaluation has to terminate successfully. If this is a
--   pay-to-pubkey output then the signature needs to match the public key that
--   locks it.
checkMatch :: ValidationMonad m => TxInfo -> InOutMatch -> m ()
checkMatch txinfo = \case
    ScriptMatch ix vl r d -> do
        let
            ptx' = ValidatorCtx { valCtxTxInfo = txinfo, valCtxInput = ix }
            vd = Context (toData ptx')
        case runExcept $ runScript vd vl d r of
            Left e  -> throwError $ ScriptFailure e
            Right _ -> pure ()
    PubKeyMatch msg pk sig -> unless (signedBy sig pk msg) $ throwError $ InvalidSignature pk sig

-- | Check if the value produced by a transaction equals the value consumed by it.
checkValuePreserved :: ValidationMonad m => Tx -> m ()
checkValuePreserved t = do
    inVal <- (P.+) (txForge t) <$> fmap fold (traverse (lkpValue . txInRef) (Set.toList $ view inputs t))
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

-- | Create the data about the transaction which will be passed to a validator script.
mkTxInfo :: ValidationMonad m => Tx -> m TxInfo
mkTxInfo tx = do
    txins <- traverse mkIn $ Set.toList $ view inputs tx
    let ptx = TxInfo
            { txInfoInputs = txins
            , txInfoOutputs = txOutputs tx
            , txInfoForge = txForge tx
            , txInfoFee = txFee tx
            , txInfoValidRange = txValidRange tx
            , txInfoForgeScripts = monetaryPolicyHash <$> Set.toList (tx ^. forgeScripts)
            , txInfoSignatories = fmap pubKeyHash $ Map.keys (tx ^. signatures)
            , txInfoData = Map.toList (tx ^. datumWitnesses)
            , txInfoId = txId tx
            }
    pure ptx

-- | Create the data about a transaction input which will be passed to a validator script.
mkIn :: ValidationMonad m => TxIn -> m Validation.TxInInfo
mkIn TxIn{txInRef, txInType} = do
    vl <- lkpValue txInRef
    pure $ case txInType of
        ConsumeScriptAddress v r d ->
            let witness = (Scripts.validatorHash v, Scripts.redeemerHash r, Scripts.datumHash d)
            in Validation.TxInInfo txInRef (Just witness) vl
        ConsumePublicKeyAddress -> Validation.TxInInfo txInRef Nothing vl
