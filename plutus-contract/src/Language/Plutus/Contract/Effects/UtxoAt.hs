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
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.UtxoAt where

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import           Data.Row
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           GHC.Generics                     (Generic)
import           Ledger                           (Address)
import           Ledger.AddressMap                (AddressMap)
import qualified Ledger.AddressMap                as AM
import           Ledger.Tx                        (TxOut, TxOutRef)

import           Language.Plutus.Contract.Request (Contract, ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)

type HasUtxoAt s =
    ( HasType "utxo-at" UtxoAtAddress (Input s)
    , HasType "utxo-at" (Set Address) (Output s)
    , ContractRow s)

data UtxoAtAddress =
  UtxoAtAddress
    { address :: Address
    , utxo    :: Map TxOutRef TxOut
    }
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

type UtxoAt = "utxo-at" .== (UtxoAtAddress, Set Address)

-- | Get the unspent transaction outputs at an address.
utxoAt :: forall s. HasUtxoAt s => Address -> Contract s AddressMap
utxoAt address' =
    let check :: UtxoAtAddress -> Maybe AddressMap
        check UtxoAtAddress{address,utxo} =
          if address' == address then Just (AM.AddressMap $ Map.singleton address utxo) else Nothing
    in
    requestMaybe @"utxo-at" @_ @_ @s (Set.singleton address') check

event
    :: forall s.
    ( HasUtxoAt s )
    => UtxoAtAddress
    -> Event s
event = Event . IsJust (Label @"utxo-at")

addresses
    :: forall s.
    ( HasUtxoAt s )
    => Handlers s
    -> Set Address
addresses (Handlers r) = r .! Label @"utxo-at"
