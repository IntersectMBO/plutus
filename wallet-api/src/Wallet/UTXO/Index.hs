{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
-- | A map of transaction hashes to transactions for efficient lookups of
--   values on the mockchain.
module Wallet.UTXO.Index(
    UtxoLookup,
    UtxoIndex(..),
    empty,
    insert,
    insertBlock,
    initialise,
    Lookup,
    runLookup,
    lookupRef,
    LookupError(..),
    validTxIndexed
    ) where

import           Control.Applicative  (liftA2)
import           Control.Monad.Except (MonadError (..), liftEither)
import           Control.Monad.Reader (MonadReader (..), ReaderT (..), ask)
import           Data.Foldable        (foldl')
import qualified Data.Map             as Map
import           Data.Semigroup       (Semigroup, Sum (..))
import qualified Data.Set             as Set
import           Prelude              hiding (lookup)
import           Wallet.UTXO.Types    (Blockchain, Tx (..), TxIn (..), TxOut (..), TxOut', TxOutRef', ValidationData,
                                       Value, unspentOutputs, updateUtxo, validValuesTx, validate)

type UtxoLookup m = (MonadReader UtxoIndex m, MonadError LookupError m)

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
lookup :: TxOutRef' -> UtxoIndex -> Either LookupError TxOut'
lookup i =
    maybe (Left $ TxOutRefNotFound i) Right . Map.lookup i . getIndex

newtype LookupError = TxOutRefNotFound TxOutRef'
    deriving (Eq)

newtype Lookup a = Lookup { _runLookup :: (ReaderT UtxoIndex (Either LookupError)) a }
    deriving (Functor, Applicative, Monad, MonadReader UtxoIndex, MonadError LookupError)

-- | Find an unspent transaction output by its reference. Assumes that the
--   output for this reference exists. If you want to handle the lookup error
--   you can use `runLookup`.
lookupRef :: UtxoLookup m => TxOutRef' -> m TxOut'
lookupRef t = liftEither  . lookup t =<< ask

-- | Run a `Lookup` on a `UtxoIndex`
runLookup :: Lookup a -> UtxoIndex -> Either LookupError a
runLookup l = runReaderT (_runLookup l)

-- | Determine the unspent value that an input refers to
value :: UtxoLookup m => TxOutRef' -> m Value
value o = txOutValue <$> lookupRef o

infixr 3 <&&>

-- | Lifted `(&&)`
(<&&>) :: Applicative f => f Bool -> f Bool -> f Bool
(<&&>) = liftA2 (&&)

-- | Validate a transaction in a `UtxoLookup` context.
--   This does the same as `Wallet.UTXO.Types.validTx`, but more efficiently as
--   it doesn't compute the UTXO of a blockchain from scratch.
--   It also gives a more precise error: A return value of `False` indicates
--   that one of the value preservation conditions is false, or that the script
--   failed. Failing with `LookupError` means that the outputs spent by the
--   transaction are not part of the UTxO set of the blockchain. In
--   `Wallet.UTXO.Types.validTx` this failure condition would also result in
--   `False`.
validTxIndexed :: UtxoLookup m => ValidationData -> Tx -> m Bool
validTxIndexed v t = valueIsPreserved t <&&> pure (validValuesTx t) <&&> inputsAreValid  where
    inputsAreValid = and <$> traverse validates (Set.toList $ txInputs t)
    validates txIn = validate v txIn <$> lookupRef (txInRef txIn)

-- | Check if the value produced by a transaction equals the value consumed by
--   it.
valueIsPreserved :: UtxoLookup m => Tx -> m Bool
valueIsPreserved t = (== outVal) <$> inVal where
    inVal =
        (txForge t +) <$> fmap (getSum . foldMap Sum) (traverse (value . txInRef) (Set.toList $ txInputs t))
    outVal =
        txFee t + sum (map txOutValue (txOutputs t))
