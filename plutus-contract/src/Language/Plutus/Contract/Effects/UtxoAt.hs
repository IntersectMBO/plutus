{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.UtxoAt where

import           Data.Aeson                                    (FromJSON, ToJSON)
import           Data.Map                                      (Map)
import qualified Data.Map                                      as Map
import           Data.Row
import           Data.Set                                      (Set)
import qualified Data.Set                                      as Set
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                                  (Generic)
import           Ledger                                        (Address, TxOut (..), TxOutTx (..))
import           Ledger.Tx                                     (TxOutRef)

import           IOTS                                          (IotsType)
import           Language.Plutus.Contract.Effects.WatchAddress (AddressSet (..))
import           Language.Plutus.Contract.Request              (Contract, ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema               (Event (..), Handlers (..), Input, Output)

type UtxoAtSym = "utxo-at"

type HasUtxoAt s =
    ( HasType UtxoAtSym UtxoAtAddress (Input s)
    , HasType UtxoAtSym AddressSet (Output s)
    , ContractRow s)

data UtxoAtAddress =
  UtxoAtAddress
    { address :: Address
    , utxo    :: Map TxOutRef TxOutTx
    }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON, IotsType)

instance Pretty UtxoAtAddress where
  pretty UtxoAtAddress{address, utxo} =
    let
      prettyTxOutPair (txoutref, TxOutTx _ TxOut{txOutValue, txOutType}) =
        pretty txoutref <> colon <+> pretty txOutType <+> viaShow txOutValue
      utxos = vsep $ fmap prettyTxOutPair (Map.toList utxo)
    in vsep ["Utxo at" <+> pretty address <+> "=", indent 2 utxos]

type UtxoAt = UtxoAtSym .== (UtxoAtAddress, AddressSet)

-- | Get the unspent transaction outputs at an address.
utxoAt :: forall s e. HasUtxoAt s => Address -> Contract s e (Map TxOutRef TxOutTx)
utxoAt address' =
    let check :: UtxoAtAddress -> Maybe (Map TxOutRef TxOutTx)
        check UtxoAtAddress{address,utxo} =
          if address' == address then Just utxo else Nothing
    in
    requestMaybe @UtxoAtSym @_ @_ @s (AddressSet $ Set.singleton address') check

event
    :: forall s.
    ( HasUtxoAt s )
    => UtxoAtAddress
    -> Event s
event = Event . IsJust (Label @UtxoAtSym)

addresses
    :: forall s.
    ( HasUtxoAt s )
    => Handlers s
    -> Set Address
addresses (Handlers r) = unAddressSet (r .! Label @UtxoAtSym)
