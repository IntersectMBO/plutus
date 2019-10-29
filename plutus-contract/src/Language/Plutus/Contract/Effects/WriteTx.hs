{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.WriteTx where

import           Control.Lens
import           Control.Monad                    ((>=>))
import           Control.Monad.Error.Lens         (throwing)
import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                     (Generic)

import           Language.Plutus.Contract.Request as Req
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Tx      (UnbalancedTx)

import           Ledger.TxId                      (TxId)
import           Wallet.API                       (WalletAPIError)

type TxSymbol = "tx"

data WriteTxResponse =
  WriteTxFailed WalletAPIError
  | WriteTxSuccess TxId
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty WriteTxResponse where
  pretty = \case
    WriteTxFailed e -> "WriteTxFailed:" <+> pretty e
    WriteTxSuccess i -> "WriteTxSuccess:" <+> viaShow i

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

-- | Send an unbalanced transaction to be balanced and signed. Returns the ID
--    of the final transaction, or an error.
writeTx :: forall s e. HasWriteTx s => UnbalancedTx -> Contract s e WriteTxResponse
writeTx t = request @TxSymbol @_ @_ @s (PendingTransactions [t])

-- | Send an unbalanced transaction to be balanced and signed. Returns the ID
--    of the final transaction, throws an error on failure.
writeTxSuccess :: forall s e. (HasWriteTx s, Req.AsContractError e) => UnbalancedTx -> Contract s e TxId
-- See Note [Injecting errors into the user's error type]
writeTxSuccess = writeTx >=> either (throwing Req._WalletError) pure . view writeTxResponse

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
