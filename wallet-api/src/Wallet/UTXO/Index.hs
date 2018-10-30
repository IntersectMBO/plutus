{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
-- | An index of unspent transaction outputs, and some functions for validating
--   transactions using the UTXO index.
module Wallet.UTXO.Index(
    ValidationMonad,
    UtxoIndex(..),
    empty,
    insert,
    insertBlock,
    initialise,
    Validation,
    runValidation,
    lookupRef,
    ValidationError(..),
    validateTransaction
    ) where

import           Control.Monad.Except (MonadError (..), liftEither)
import           Control.Monad.Reader (MonadReader (..), ReaderT (..), ask)
import           Data.Foldable        (foldl', traverse_)
import qualified Data.Map             as Map
import           Data.Semigroup       (Semigroup, Sum (..))
import qualified Data.Set             as Set
import           GHC.Generics         (Generic)
import           Prelude              hiding (lookup)
import           Wallet.UTXO.Types    (Blockchain, DataScript, PubKey, Signature, Tx (..), TxIn (..), TxIn', TxOut (..),
                                       TxOut', TxOutRef', ValidationData, Value, unspentOutputs, updateUtxo,
                                       validValuesTx)
import qualified Wallet.UTXO.Types    as UTXO

-- | Context for validating transactions. We need access to the unspent
--   transaction outputs of the blockchain, and we can throw `ValidationError`s
type ValidationMonad m = (MonadReader UtxoIndex m, MonadError ValidationError m)

-- | The transactions of a blockchain indexed by hash
newtype UtxoIndex = UtxoIndex { getIndex :: Map.Map TxOutRef' TxOut' }
    deriving (Eq, Ord, Show, Semigroup)

-- | An empty [[UtxoIndex]]
empty :: UtxoIndex
empty = UtxoIndex Map.empty

-- | Create an index of all transactions on the chain
initialise :: Blockchain -> UtxoIndex
initialise = UtxoIndex . unspentOutputs

-- | Add a transaction to the index
insert :: Tx -> UtxoIndex -> UtxoIndex
insert tx = UtxoIndex . updateUtxo tx . getIndex

-- | Add a block of transactions to the index
insertBlock :: [Tx] -> UtxoIndex -> UtxoIndex
insertBlock blck i = foldl' (flip insert) i blck

-- | Find an unspent transaction output by the `TxOutRef'` that spends it.
lookup :: TxOutRef' -> UtxoIndex -> Either ValidationError TxOut'
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
    -- ^ Evaluation of the validator script failed
    deriving (Eq, Show, Generic)

newtype Validation a = Validation { _runValidation :: (ReaderT UtxoIndex (Either ValidationError)) a }
    deriving (Functor, Applicative, Monad, MonadReader UtxoIndex, MonadError ValidationError)

-- | Find an unspent transaction output by its reference. Assumes that the
--   output for this reference exists. If you want to handle the lookup error
--   you can use `runLookup`.
lookupRef :: ValidationMonad m => TxOutRef' -> m TxOut'
lookupRef t = liftEither  . lookup t =<< ask

-- | Run a `Validation` on a `UtxoIndex`
runValidation :: Validation a -> UtxoIndex -> Either ValidationError a
runValidation l = runReaderT (_runValidation l)

-- | Determine the unspent value that an input refers to
value :: ValidationMonad m => TxOutRef' -> m Value
value o = txOutValue <$> lookupRef o

-- | Validate a transaction in a `UtxoLookup` context.
--
--   This does the same as `Wallet.UTXO.Types.validTx`, but more efficiently as
--   it doesn't compute the UTXO of a blockchain from scratch.
--   It also gives a more precise error: `ValidationError` instead of `False`.
validateTransaction :: ValidationMonad m
    => ValidationData
    -> Tx
    -> m ()
validateTransaction v t =
    checkValuePreserved t >> checkPositiveValues t >> checkValidInputs v t

-- | Check if the inputs of the transaction consume outputs that
--   (a) exist and
--   (b) can be unlocked by the signatures or validator scripts of the inputs
checkValidInputs :: ValidationMonad m => ValidationData -> Tx -> m ()
checkValidInputs v = traverse_ (checkValidInput v) . Set.toList . txInputs

-- | Validate a single transaction input
checkValidInput :: ValidationMonad m => ValidationData -> TxIn' -> m ()
checkValidInput v i = (lookupRef $ txInRef i) >>= checkInputOutput v i

-- | Check that a transaction output can be spent by a transaction input
checkInputOutput :: ValidationMonad m => ValidationData -> TxIn' -> TxOut' -> m ()
checkInputOutput bs i txo =
    case (txInType i, txOutType txo) of
        (UTXO.ConsumeScriptAddress v r, UTXO.PayToScript d)
            | txOutAddress txo /= UTXO.scriptAddress (txOutValue txo) v d ->
                throwError $ InvalidScriptHash d
            | otherwise ->
                if UTXO.runScript bs v r d
                then pure ()
                else throwError ScriptFailure
        (UTXO.ConsumePublicKeyAddress sig, UTXO.PayToPubKey pk) ->
            if sig `UTXO.signedBy` pk
            then pure ()
            else throwError $ InvalidSignature pk sig
        _ -> throwError $ InOutTypeMismatch i txo

-- | Check if the value produced by a transaction equals the value consumed by
--   it.
checkValuePreserved :: ValidationMonad m => Tx -> m ()
checkValuePreserved t = do
    inVal <- (txForge t +) <$> fmap (getSum . foldMap Sum) (traverse (value . txInRef) (Set.toList $ txInputs t))
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
