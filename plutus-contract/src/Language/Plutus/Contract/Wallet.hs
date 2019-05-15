{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Balance  `UnbalancedTx` values using the
--   wallet API
module Language.Plutus.Contract.Wallet(
      balanceWallet
    , balanceTx
    , handleTx
    , WAPI.startWatching
    ) where

import           Control.Lens
import           Control.Monad                        ((>=>))
import           Control.Monad.Except
import           Data.Bifunctor                       (second)
import           Data.Map                             (Map)
import qualified Data.Map                             as Map
import           Data.Maybe                           (fromMaybe)
import qualified Data.Set                             as Set
import           Data.String                          (IsString (fromString))
import           Language.Plutus.Contract.Transaction (UnbalancedTx)
import qualified Language.Plutus.Contract.Transaction as T
import qualified Ledger.AddressMap                    as AM
import           Ledger.Tx                            (Tx, TxOut, TxOutRef)
import qualified Ledger.Tx                            as Tx
import           Ledger.Value                         (Value)
import qualified Ledger.Value                         as Value
import           Wallet.API                           (MonadWallet, PubKey, WalletAPIError)
import qualified Wallet.API                           as WAPI
import qualified Wallet.Emulator                      as E

-- | Balance an unbalanced transaction in a 'MonadWallet' context.
balanceWallet
    :: (WAPI.MonadWallet m)
    => UnbalancedTx
    -> m Tx
balanceWallet utx = do
    WAPI.logMsg "Balancing an unbalanced transaction."
    pk <- WAPI.ownPubKey
    addr <- WAPI.watchedAddresses
    let utxo = addr ^. at (Tx.pubKeyAddress pk) . to (fromMaybe mempty)
    balanceTx utxo pk utx

-- | Compute the difference between the value of the inputs consumed and the
--   value of the outputs produced by the transaction. If the result is zero
--   then the transaction is balanced.
--
--   Fails if the unbalanced transaction contains an input the spends an output
--   unknown to the wallet.
computeBalance :: WAPI.MonadWallet m => UnbalancedTx -> m Value
computeBalance utx = Value.minus <$> left <*> pure right  where
    right = foldMap (view Tx.outValue) (utx ^. T.outputs)
    left = foldM go Value.zero (utx ^. T.inputs)
    go cur inp = do
        am <- WAPI.watchedAddresses
        let txout = AM.outRefMap am ^. at (Tx.txInRef inp)
        case txout of
            Just vl -> pure (cur `Value.plus` Tx.txOutValue vl)
            Nothing ->
                WAPI.throwOtherError $ "Unable to find TxOut for " <> fromString (show inp)

    -- right `V.minus` left where
    -- left = (utx ^. forge) `V.plus` foldMap snd (utx ^. inputs)

-- | Balance an unbalanced transaction by adding public key inputs
--   and outputs
balanceTx
    :: ( WAPI.MonadWallet m )
    => Map TxOutRef TxOut
    -- ^ Unspent transaction outputs that may be used to balance the
    --   left hand side (inputs) of the transaction.
    -> PubKey
    -- ^ Public key, used to balance the right hand side (outputs) of
    --   the transaction.
    -> UnbalancedTx
    -- ^ The unbalanced transaction
    -> m Tx
balanceTx utxo pk tx = do
    (neg, pos) <- Value.split <$> computeBalance tx
    let tx' = addOutputs pk pos (T.toLedgerTx tx)
    if Value.isZero neg
    then pure tx'
    else addInputs utxo pk neg tx'

-- | @addInputs mp pk vl tx@ selects transaction outputs worth at least
--   @vl@ from the UTXO map @mp@ and adds them as inputs to @tx@. A public
--   key output for @pk@ is added containing any leftover change.
addInputs
    :: MonadError WalletAPIError m
    => Map TxOutRef TxOut
    -> PubKey
    -> Value
    -> Tx
    -> m Tx
addInputs mp pk vl tx = do
    (spend, change) <- E.selectCoin (second Tx.txOutValue <$> Map.toList mp) vl
    let

        addTxIns  =
            let ins = Set.fromList (flip Tx.pubKeyTxIn pk . fst <$> spend)
            in over Tx.inputs (Set.union ins)

        addTxOuts = if change == Value.zero
                    then id
                    else addOutputs pk change

    pure $ tx & addTxOuts & addTxIns

addOutputs :: PubKey -> Value -> Tx -> Tx
addOutputs pk vl tx = tx & over Tx.outputs (pko :) where
    pko = Tx.pubKeyTxOut vl pk

-- | Balance an unabalanced transaction, sign it, and submit
--   it to the chain in the context of a wallet. Note that this
--   only attaches a single signature to the transaction before
--   submitting it. Hence the `requiredSignatures` field of the
--   unbalanced transaction is ignored.
handleTx :: MonadWallet m => UnbalancedTx -> m ()
handleTx = balanceWallet >=> WAPI.signTxAndSubmit_
