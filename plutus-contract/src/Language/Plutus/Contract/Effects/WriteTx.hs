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
import           Control.Monad.Error.Lens                          (throwing)
import           Data.Aeson                                        (FromJSON, ToJSON)
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                                      (Generic)

import           Language.Plutus.Contract.Effects.AwaitTxConfirmed (HasTxConfirmation, awaitTxConfirmed)
import           Language.Plutus.Contract.Request                  as Req
import           Language.Plutus.Contract.Schema                   (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Tx                       (UnbalancedTx)

import           IOTS                                              (IotsType)
import           Ledger.TxId                                       (TxId)
import           Wallet.API                                        (WalletAPIError)

type TxSymbol = "tx"

data WriteTxResponse =
  WriteTxFailed WalletAPIError
  | WriteTxSuccess TxId
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty WriteTxResponse where
  pretty = \case
    WriteTxFailed e -> "WriteTxFailed:" <+> pretty e
    WriteTxSuccess i -> "WriteTxSuccess:" <+> pretty i

writeTxResponse :: Iso' WriteTxResponse (Either WalletAPIError TxId)
writeTxResponse = iso f g where
  f = \case { WriteTxFailed w -> Left w; WriteTxSuccess t -> Right t }
  g = either WriteTxFailed WriteTxSuccess

type HasWriteTx s =
    ( HasType TxSymbol WriteTxResponse (Input s)
    , HasType TxSymbol PendingTransactions (Output s)
    , ContractRow s)

type WriteTx = TxSymbol .== (WriteTxResponse, PendingTransactions)

newtype PendingTransactions =
  PendingTransactions { unPendingTransactions :: [UnbalancedTx] }
    deriving stock (Eq, Generic, Show)
    deriving newtype (Semigroup, Monoid, ToJSON, FromJSON)
    deriving Pretty via (PrettyFoldable [] UnbalancedTx)
    deriving anyclass (IotsType)

-- | Send an unbalanced transaction to be balanced and signed. Returns the ID
--    of the final transaction when the transaction was submitted. Throws an
--    error if balancing or signing failed.
submitTx :: forall s e. (HasWriteTx s, Req.AsContractError e) => UnbalancedTx -> Contract s e TxId
-- See Note [Injecting errors into the user's error type]
submitTx t =
  let req = request @TxSymbol @_ @_ @s (PendingTransactions [t]) in
  req >>= either (throwing Req._WalletError) pure . view writeTxResponse

-- | A version of 'submitTx' that waits until the transaction has been
--   confirmed on the ledger before returning.
submitTxConfirmed
  :: forall s e.
  ( HasWriteTx s
  , HasTxConfirmation s
  , Req.AsContractError e
  )
  => UnbalancedTx
  -> Contract s e ()
submitTxConfirmed t = submitTx t >>= awaitTxConfirmed

event
  :: forall s. (HasType TxSymbol WriteTxResponse (Input s), AllUniqueLabels (Input s))
  => WriteTxResponse
  -> Event s
event r = Event (IsJust #tx r)

transactions
  :: forall s. ( HasType TxSymbol PendingTransactions (Output s) )
   => Handlers s
   -> [UnbalancedTx]
transactions (Handlers r) = unPendingTransactions $ r .! #tx
