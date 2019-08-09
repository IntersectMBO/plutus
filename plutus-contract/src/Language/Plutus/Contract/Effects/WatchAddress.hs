{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.WatchAddress where

import           Control.Lens                               (at, (^.))
import           Data.Aeson                                 (FromJSON, ToJSON)
import           Data.Map                                   (Map)
import qualified Data.Map                                   as Map
import           Data.Maybe                                 (fromMaybe)
import           Data.Row
import           Data.Set                                   (Set)
import qualified Data.Set                                   as Set
import           GHC.Generics                               (Generic)
import           Ledger                                     (Address, Slot, Value)
import           Ledger.AddressMap                          (AddressMap)
import qualified Ledger.AddressMap                          as AM
import           Ledger.Tx                                  (Tx)
import qualified Ledger.Value                               as V

import           Language.Plutus.Contract.Effects.AwaitSlot
import           Language.Plutus.Contract.Request           (Contract, ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema            (Event (..), First, Hooks (..), Second)
import           Language.Plutus.Contract.Util              (loopM)

type HasWatchAddress s =
    ( HasType "address" (Address, Tx) (First s)
    , HasType "address" (Set Address) (Second s)
    , ContractRow s)

type WatchAddress = "address" .== ((Address, Tx), Set Address)

newtype InterestingAddresses =
    InterestingAddresses  { unInterestingAddresses :: Set Address }
        deriving stock (Eq, Ord, Generic, Show)
        deriving newtype (Semigroup, Monoid, ToJSON, FromJSON)

-- | Wait for the next transaction that changes an address.
nextTransactionAt :: forall s. HasWatchAddress s => Address -> Contract s Tx
nextTransactionAt addr =
    let s = Set.singleton addr
        check :: (Address, Tx) -> Maybe Tx
        check (addr', tx) = if addr == addr' then Just tx else Nothing
    in
    requestMaybe @"address" @_ @_ @s s check

-- | Watch an address until the given slot, then return all known outputs
--   at the address.
watchAddressUntil
    :: forall s.
       ( HasAwaitSlot s
       , HasWatchAddress s
       )
    => Address
    -> Slot
    -> Contract s AddressMap
watchAddressUntil a = collectUntil @s AM.updateAddresses (AM.addAddress a mempty) (nextTransactionAt @s a)

-- | Watch an address for changes, and return the outputs
--   at that address when the total value at the address
--   has surpassed the given value.
fundsAtAddressGt
    :: forall s.
       HasWatchAddress s
    => Address
    -> Value
    -> Contract s AddressMap
fundsAtAddressGt addr' vl = loopM go mempty where
    go cur = do
        delta <- AM.fromTxOutputs <$> nextTransactionAt @s addr'
        let cur' = cur <> delta
            presentVal = fromMaybe mempty (AM.values cur' ^. at addr')
        if presentVal `V.gt` vl
        then pure (Right cur') else pure (Left cur')

events
    :: forall s.
       ( HasType "address" (Address, Tx) (First s)
       , AllUniqueLabels (First s)
       )
    => AddressMap
    -> Tx
    -> Map Address (Event s)
events utxo tx =
    Map.fromSet
        (\addr -> Event $ IsJust (Label @"address") (addr, tx))
        (AM.addressesTouched utxo tx)

addresses
    :: forall s.
    ( HasType "address" (Set Address) (Second s))
    => Hooks s
    -> Set Address
addresses (Hooks r) = r .! Label @"address"
