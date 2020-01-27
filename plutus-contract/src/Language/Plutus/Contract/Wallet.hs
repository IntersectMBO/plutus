{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
-- | Balance  `UnbalancedTx` values using the
--   wallet API.
module Language.Plutus.Contract.Wallet(
      balanceWallet
    , balanceTx
    , handleTx
    , WAPI.startWatching
    , SigningProcess(..)
    , defaultSigningProcess
    , signWallet
    , signWallets
    ) where

import           Control.Lens
import           Control.Monad.Except
import qualified Control.Monad.Freer         as Eff
import qualified Control.Monad.Freer.Error   as Eff
import           Data.Bifunctor              (second)
import           Data.Map                    (Map)
import qualified Data.Map                    as Map
import           Data.Maybe                  (fromMaybe)
import qualified Data.Set                    as Set
import           Data.String                 (IsString (fromString))
import           Data.Text.Prettyprint.Doc   (Pretty (..))
import           Language.Plutus.Contract.Tx (UnbalancedTx)
import qualified Language.Plutus.Contract.Tx as T
import qualified Language.PlutusTx.Numeric   as N
import qualified Language.PlutusTx.Prelude   as P
import qualified Ledger                      as L
import qualified Ledger.AddressMap           as AM
import           Ledger.Tx                   (Tx, TxOut, TxOutRef)
import qualified Ledger.Tx                   as Tx
import           Ledger.Value                (Value)
import qualified Ledger.Value                as Value
import           Wallet.API                  (MonadWallet, PubKey, WalletAPIError)
import qualified Wallet.API                  as WAPI
import           Wallet.Emulator             (Wallet)
import qualified Wallet.Emulator             as E

-- | Balance an unbalanced transaction in a 'MonadWallet' context. See note
--   [Unbalanced transactions].
balanceWallet
    :: (WAPI.MonadWallet m)
    => UnbalancedTx
    -> m Tx
balanceWallet utx = do
    WAPI.logMsg $ "Balancing an unbalanced transaction: " <> fromString (show $ pretty utx)
    pk <- WAPI.ownPubKey
    addr <- WAPI.watchedAddresses
    let utxo = addr ^. at (L.pubKeyAddress pk) . to (fromMaybe mempty)
    balanceTx (fmap Tx.txOutTxOut utxo) pk utx

-- | Compute the difference between the value of the inputs consumed and the
--   value of the outputs produced by the transaction. If the result is zero
--   then the transaction is balanced.
--
--   Fails if the unbalanced transaction contains an input that spends an output
--   unknown to the wallet.
computeBalance :: WAPI.MonadWallet m => Tx -> m Value
computeBalance tx = (P.-) <$> left <*> pure right  where
    right = L.txFee tx P.+ foldMap (view Tx.outValue) (tx ^. Tx.outputs)
    left = do
        inputValues <- traverse lookupValue (Set.toList $ Tx.txInputs tx)
        pure $ foldr (P.+) P.zero (L.txForge tx : inputValues)
    lookupValue outputRef = do
        am <- WAPI.watchedAddresses
        let txout = AM.outRefMap am ^. at (Tx.txInRef outputRef)
        case txout of
            Just out -> pure $ Tx.txOutValue $ Tx.txOutTxOut out
            Nothing ->
                WAPI.throwOtherError $ "Unable to find TxOut for " <> fromString (show outputRef)

-- | Balance an unbalanced transaction by adding public key inputs
--   and outputs.
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
balanceTx utxo pk utx = do
    let tx0 = T.toLedgerTx utx
        tx = addMissingValueMoved pk (T.valueMoved utx) tx0
    (neg, pos) <- Value.split <$> computeBalance tx

    tx' <- if Value.isZero pos
           then pure tx
           else do
                   WAPI.logMsg $ "Adding public key output for " <> fromString (show pos)
                   pure $ addOutputs pk pos tx

    if Value.isZero neg
    then pure tx'
    else do
        WAPI.logMsg $ "Adding inputs for " <> fromString (show neg)
        addInputs utxo pk neg tx'

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
    (spend, change) <- liftEither $ Eff.run $ Eff.runError $ E.selectCoin (second Tx.txOutValue <$> Map.toList mp) vl
    let

        addTxIns  =
            let ins = Set.fromList (Tx.pubKeyTxIn . fst <$> spend)
            in over Tx.inputs (Set.union ins)

        addTxOuts = if Value.isZero change
                    then id
                    else addOutputs pk change

    pure $ tx & addTxOuts & addTxIns

addOutputs :: PubKey -> Value -> Tx -> Tx
addOutputs pk vl tx = tx & over Tx.outputs (pko :) where
    pko = Tx.pubKeyTxOut vl pk

addMissingValueMoved :: PubKey -> Value -> Tx -> Tx
addMissingValueMoved pk vl tx =
    let total = foldMap (view Tx.outValue) (view Tx.outputs tx)
        -- 'missing' is everything that's in
        -- 'vl' but not in 'total'
        (_, missing) = Value.split (vl N.- total)
    in if Value.isZero missing
       then tx
       else addOutputs pk missing tx

-- | Balance an unabalanced transaction, sign it, and submit
--   it to the chain in the context of a wallet.
handleTx :: MonadWallet m => SigningProcess -> UnbalancedTx -> m Tx
handleTx p utx =
    balanceWallet utx >>= addSignatures p (T.requiredSignatories utx) >>= WAPI.signTxAndSubmit

-- | The signing process gets a finished transaction and a list of public keys,
--   and signs the transaction with the corresponding private keys.
newtype SigningProcess = SigningProcess { addSignatures :: forall m. MonadWallet m => [L.PubKeyHash] -> Tx -> m Tx }

-- | The default signing process is 'signWallet'
defaultSigningProcess :: SigningProcess
defaultSigningProcess = signWallet

-- | Sign the transaction by calling 'WAPI.signTxnWithKey' (throwing a
--   'PrivateKeyNotFound' error if called with a key other than the
--   wallet's private key)
signWallet :: SigningProcess
signWallet = SigningProcess $
    \pks tx -> foldM WAPI.signTxnWithKey tx pks

-- | Sign the transaction with the private keys of the given wallets,
--   ignoring the list of public keys that the 'SigningProcess' is passed.
signWallets :: [Wallet] -> SigningProcess
signWallets wallets = SigningProcess $ \_ tx ->
    let signingKeys = E.walletPrivKey <$> wallets in
    pure (foldr Tx.addSignature tx signingKeys)
