{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.UtxoAt where

import           Data.Aeson                                 (FromJSON, ToJSON)
import qualified Data.Map                                   as Map
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                               (Generic)
import           Ledger                                     (Address, Slot, TxOut (..), TxOutTx (..))
import           Ledger.AddressMap                          (UtxoMap)

import           Language.Plutus.Contract.Effects.AwaitSlot (HasAwaitSlot, awaitSlot)
import           Language.Plutus.Contract.Request           (ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema            (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types             (AsContractError, Contract)

type UtxoAtSym = "utxo-at"

type HasUtxoAt s =
    ( HasType UtxoAtSym UtxoAtAddress (Input s)
    , HasType UtxoAtSym Address (Output s)
    , ContractRow s)

data UtxoAtAddress =
  UtxoAtAddress
    { address :: Address
    , utxo    :: UtxoMap
    }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Pretty UtxoAtAddress where
  pretty UtxoAtAddress{address, utxo} =
    let
      prettyTxOutPair (txoutref, TxOutTx _ TxOut{txOutValue, txOutType}) =
        pretty txoutref <> colon <+> pretty txOutType <+> viaShow txOutValue
      utxos = vsep $ fmap prettyTxOutPair (Map.toList utxo)
    in vsep ["Utxo at" <+> pretty address <+> "=", indent 2 utxos]

type UtxoAt = UtxoAtSym .== (UtxoAtAddress, Address)

-- | Get the unspent transaction outputs at an address.
utxoAt :: forall w s e. (AsContractError e, HasUtxoAt s) => Address -> Contract w s e UtxoMap
utxoAt address' =
    let check :: UtxoAtAddress -> Maybe UtxoMap
        check UtxoAtAddress{address,utxo} =
          if address' == address then Just utxo else Nothing
    in
    requestMaybe @w @UtxoAtSym @_ @_ @s address' check

event
    :: forall s.
    ( HasUtxoAt s )
    => UtxoAtAddress
    -> Event s
event = Event . IsJust (Label @UtxoAtSym)

utxoAtRequest
    :: forall s.
    ( HasUtxoAt s )
    => Handlers s
    -> Maybe Address
utxoAtRequest (Handlers r) = trial' r (Label @UtxoAtSym)

-- | Watch an address until the given slot, then return all known outputs
--   at the address.
watchAddressUntil
    :: forall w s e.
       ( HasAwaitSlot s
       , HasUtxoAt s
       , AsContractError e
       )
    => Address
    -> Slot
    -> Contract w s e UtxoMap
watchAddressUntil a slot = awaitSlot slot >> utxoAt a
