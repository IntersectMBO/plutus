{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.WriteTx where

import           Control.Lens
import           Data.Aeson                                        (FromJSON, ToJSON)
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           Data.Void                                         (Void)
import           GHC.Generics                                      (Generic)

import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (HasTxConfirmation, awaitTxConfirmed)
import           Language.Plutus.Contract.Request                  as Req
import           Language.Plutus.Contract.Schema                   (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types                    (AsContractError, Contract,
                                                                    _ConstraintResolutionError, _WalletError,
                                                                    throwError)
import qualified Language.PlutusTx                                 as PlutusTx

import           Ledger.AddressMap                                 (UtxoMap)
import           Ledger.Constraints                                (TxConstraints)
import           Ledger.Constraints.OffChain                       (ScriptLookups, UnbalancedTx)
import qualified Ledger.Constraints.OffChain                       as Constraints
import           Ledger.Tx                                         (Tx, txId)
import           Ledger.Typed.Scripts                              (ScriptInstance, ScriptType (..))

import           Wallet.API                                        (WalletAPIError)

type TxSymbol = "tx"

data WriteTxResponse =
  WriteTxFailed WalletAPIError
  | WriteTxSuccess Tx
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty WriteTxResponse where
  pretty = \case
    WriteTxFailed e  -> "WriteTxFailed:" <+> pretty e
    WriteTxSuccess i -> "WriteTxSuccess:" <+> pretty (txId i)

writeTxResponse :: Iso' WriteTxResponse (Either WalletAPIError Tx)
writeTxResponse = iso f g where
  f = \case { WriteTxFailed w -> Left w; WriteTxSuccess t -> Right t }
  g = either WriteTxFailed WriteTxSuccess

type HasWriteTx s =
    ( HasType TxSymbol WriteTxResponse (Input s)
    , HasType TxSymbol UnbalancedTx (Output s)
    , ContractRow s)

type WriteTx = TxSymbol .== (WriteTxResponse, UnbalancedTx)

-- | Send an unbalanced transaction to be balanced and signed. Returns the ID
--    of the final transaction when the transaction was submitted. Throws an
--    error if balancing or signing failed.
submitUnbalancedTx :: forall s e. (AsContractError e, HasWriteTx s) => UnbalancedTx -> Contract s e Tx
-- See Note [Injecting errors into the user's error type]
submitUnbalancedTx t =
  let req = request @TxSymbol @_ @_ @s t in
  req >>= either (throwError . review _WalletError) pure . view writeTxResponse

-- | Build a transaction that satisfies the constraints, then submit it to the
--   network. The constraints do not refer to any typed script inputs or
--   outputs.
submitTx :: forall s e.
  ( HasWriteTx s
  , AsContractError e
  )
  => TxConstraints Void Void
  -> Contract s e Tx
submitTx = submitTxConstraintsWith @Void mempty

-- | Build a transaction that satisfies the constraints, then submit it to the
--   network. Using the current outputs at the contract address and the
--   contract's own public key to solve the constraints.
submitTxConstraints
  :: forall a s e.
  ( HasWriteTx s
  , PlutusTx.IsData (RedeemerType a)
  , PlutusTx.IsData (DatumType a)
  , AsContractError e
  )
  => ScriptInstance a
  -> TxConstraints (RedeemerType a) (DatumType a)
  -> Contract s e Tx
submitTxConstraints inst = submitTxConstraintsWith (Constraints.scriptInstanceLookups inst)

-- | Build a transaction that satisfies the constraints using the UTXO map
--   to resolve any input constraints (see 'Ledger.Constraints.TxConstraints.InputConstraint')
submitTxConstraintsSpending
  :: forall a s e.
  ( HasWriteTx s
  , PlutusTx.IsData (RedeemerType a)
  , PlutusTx.IsData (DatumType a)
  , AsContractError e
  )
  => ScriptInstance a
  -> UtxoMap
  -> TxConstraints (RedeemerType a) (DatumType a)
  -> Contract s e Tx
submitTxConstraintsSpending inst utxo =
  let lookups = Constraints.scriptInstanceLookups inst <> Constraints.unspentOutputs utxo
  in submitTxConstraintsWith lookups

-- | Build a transaction that satisfies the constraints, then submit it to the
--   network. Using the given constraints.
submitTxConstraintsWith
  :: forall a s e.
  ( HasWriteTx s
  , PlutusTx.IsData (RedeemerType a)
  , PlutusTx.IsData (DatumType a)
  , AsContractError e
  )
  => ScriptLookups a
  -> TxConstraints (RedeemerType a) (DatumType a)
  -> Contract s e Tx
submitTxConstraintsWith sl constraints = do
  tx <- either (throwError . review _ConstraintResolutionError) pure (Constraints.mkTx sl constraints)
  submitUnbalancedTx tx

-- | A version of 'submitTx' that waits until the transaction has been
--   confirmed on the ledger before returning.
submitTxConfirmed
  :: forall s e.
  ( HasWriteTx s
  , HasTxConfirmation s
  , AsContractError e
  )
  => UnbalancedTx
  -> Contract s e ()
submitTxConfirmed t = submitUnbalancedTx t >>= awaitTxConfirmed . txId

event
  :: forall s. (HasType TxSymbol WriteTxResponse (Input s), AllUniqueLabels (Input s))
  => WriteTxResponse
  -> Event s
event r = Event (IsJust #tx r)

pendingTransaction
  :: forall s. ( HasType TxSymbol UnbalancedTx (Output s) )
   => Handlers s
   -> Maybe UnbalancedTx
pendingTransaction (Handlers r) = trial' r (Label @TxSymbol)
