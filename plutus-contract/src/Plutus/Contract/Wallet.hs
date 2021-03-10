{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
-- | Turn 'UnbalancedTx' values into transactions using the
--   wallet API.
module Language.Plutus.Contract.Wallet(
      balanceWallet
    , balanceTx
    , handleTx
    , WAPI.startWatching
    ) where

import           Control.Lens
import           Control.Monad.Freer            (Eff, Member)
import           Control.Monad.Freer.Error      (Error)
import           Control.Monad.Freer.Extras.Log (LogMsg, logDebug, logInfo)
import           Data.Bifunctor                 (second)
import qualified Data.Map                       as Map
import qualified Data.Set                       as Set
import           Data.String                    (IsString (fromString))
import qualified Language.PlutusTx.Prelude      as P
import qualified Ledger                         as L
import           Ledger.AddressMap              (UtxoMap)
import qualified Ledger.AddressMap              as AM
import           Ledger.Constraints.OffChain    (UnbalancedTx (..))
import           Ledger.Tx                      (Tx (..))
import qualified Ledger.Tx                      as Tx
import           Ledger.Value                   (Value)
import qualified Ledger.Value                   as Value
import           Wallet.API                     (PubKey, WalletAPIError)
import qualified Wallet.API                     as WAPI
import           Wallet.Effects
import qualified Wallet.Emulator                as E
import           Wallet.Emulator.LogMessages    (TxBalanceMsg (..))

{- Note [Submitting transactions from Plutus contracts]

'UnbalancedTx' is the type of transactions that meet some set of constraints
(produced by 'Ledger.Constraints.OffChain.mkTx'), but can't be submitted to
the ledger yet because they may not be balanced and they lack signatures and
fee payments. To turn an 'UnbalancedTx' value into a valid transaction that can
be submitted to the network, the contract backend needs to

* Balance it.
  If the total value of 'txInputs' + the 'txForge' field is
  greater than the total value of 'txOutputs', then one or more public key
  outputs need to be added. How many and what addresses they are is up
  to the wallet (probably configurable).
  If the total balance 'txInputs' + the 'txForge' field is less than
  the total value of 'txOutputs', then one or more public key inputs need
  to be added (and potentially some outputs for the change).

* Compute fees.
  Once the final size of the transaction is known, the fees for the transaction
  can be computed. The transaction fee needs to be paid for with additional
  inputs so I assume that this step and the previous step will be combined.

  Also note that even if the 'UnbalancedTx' that we get from the contract
  endpoint happens to be balanced already, we still need to add fees to it. So
  we can't skip the balancing & fee computation step.

  Balancing and coin selection will eventually be performed by the wallet
  backend.

* Sign it.
  The signing process needs to provide signatures for all public key
  inputs in the balanced transaction, and for all public keys in the
  'unBalancedTxRequiredSignatories' field.

-}

-- | Balance an unbalanced transaction in a 'WalletEffects' context. See note
--   [Submitting transactions from Plutus contracts].
balanceWallet ::
   ( Member WalletEffect effs
    , Member (Error WalletAPIError) effs
    , Member ChainIndexEffect effs
    , Member (LogMsg TxBalanceMsg) effs
    )
    => UnbalancedTx
    -> Eff effs Tx
balanceWallet utx = do
    logInfo $ BalancingUnbalancedTx utx
    pk <- ownPubKey
    outputs <- ownOutputs
    balanceTx outputs pk utx

-- | Compute the difference between the value of the inputs consumed and the
--   value of the outputs produced by the transaction. If the result is zero
--   then the transaction is balanced.
--
--   Fails if the unbalanced transaction contains an input that spends an output
--   unknown to the wallet.
computeBalance ::
    ( Member WalletEffect effs
    , Member (Error WalletAPIError) effs
    , Member ChainIndexEffect effs
    )
    => Tx -> Eff effs Value
computeBalance tx = (P.-) <$> left <*> pure right  where
    right = L.txFee tx P.+ foldMap (view Tx.outValue) (tx ^. Tx.outputs)
    left = do
        inputValues <- traverse lookupValue (Set.toList $ Tx.txInputs tx)
        pure $ foldr (P.+) P.zero (L.txForge tx : inputValues)
    lookupValue outputRef = do
        walletIndex <- WAPI.ownOutputs
        chainIndex <- AM.outRefMap <$> WAPI.watchedAddresses
        let txout = (walletIndex <> chainIndex) ^. at (Tx.txInRef outputRef)
        case txout of
            Just out -> pure $ Tx.txOutValue $ Tx.txOutTxOut out
            Nothing ->
                WAPI.throwOtherError $ "Unable to find TxOut for " <> fromString (show outputRef)

-- | Balance an unbalanced transaction by adding public key inputs
--   and outputs.
balanceTx ::
    ( Member WalletEffect effs
    , Member (Error WalletAPIError) effs
    , Member ChainIndexEffect effs
    , Member (LogMsg TxBalanceMsg) effs
    )
    => UtxoMap
    -- ^ Unspent transaction outputs that may be used to balance the
    --   left hand side (inputs) of the transaction.
    -> PubKey
    -- ^ Public key, used to balance the right hand side (outputs) of
    --   the transaction.
    -> UnbalancedTx
    -- ^ The unbalanced transaction
    -> Eff effs Tx
balanceTx utxo pk UnbalancedTx{unBalancedTxTx} = do
    (neg, pos) <- Value.split <$> computeBalance unBalancedTxTx

    tx' <- if Value.isZero pos
           then do
               logDebug NoOutputsAdded
               pure unBalancedTxTx
           else do
                   logDebug $ AddingPublicKeyOutputFor pos
                   pure $ addOutputs pk pos unBalancedTxTx

    if Value.isZero neg
    then do
        logDebug NoInputsAdded
        pure tx'
    else do
        logDebug $ AddingInputsFor neg
        addInputs utxo pk neg tx'

-- | @addInputs mp pk vl tx@ selects transaction outputs worth at least
--   @vl@ from the UTXO map @mp@ and adds them as inputs to @tx@. A public
--   key output for @pk@ is added containing any leftover change.
addInputs
    :: Member (Error WalletAPIError) effs
    => UtxoMap
    -> PubKey
    -> Value
    -> Tx
    -> Eff effs Tx
addInputs mp pk vl tx = do
    (spend, change) <- E.selectCoin (second (Tx.txOutValue . Tx.txOutTxOut) <$> Map.toList mp) vl
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

-- | Balance an unabalanced transaction, sign it, and submit
--   it to the chain in the context of a wallet.
handleTx :: (Member WalletEffect effs, Member ChainIndexEffect effs, Member (LogMsg TxBalanceMsg) effs, Member (Error WalletAPIError) effs) => UnbalancedTx -> Eff effs Tx
handleTx utx =
    balanceWallet utx >>= WAPI.signTxAndSubmit
