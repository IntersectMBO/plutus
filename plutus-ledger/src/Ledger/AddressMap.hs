{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE Rank2Types         #-}
{-# LANGUAGE TypeFamilies       #-}
-- | 'AddressMap's and functions for working on them.
--
-- 'AddressMap's are used to represent the limited knowledge about the state of the ledger that
-- the wallet retains. Rather than keeping the entire ledger (which can be very large) the wallet
-- only tracks the UTxOs at particular addresses.
module Ledger.AddressMap(
    AddressMap(..),
    UtxoMap,
    addAddress,
    addAddresses,
    filterRefs,
    fundsAt,
    values,
    traverseWithKey,
    singleton,
    fromTxOutputs,
    knownAddresses,
    updateAddresses,
    updateAllAddresses,
    restrict,
    addressesTouched,
    outRefMap,
    fromChain
    ) where

import           Codec.Serialise.Class    (Serialise)
import           Control.Lens             (At (..), Index, IxValue, Ixed (..), Lens', at, lens, non, view, (&), (.~),
                                           (^.))
import           Control.Monad            (join)
import           Data.Aeson               (FromJSON (..), ToJSON (..))
import qualified Data.Aeson               as JSON
import qualified Data.Aeson.Extras        as JSON
import           Data.Foldable            (fold)
import           Data.Map                 (Map)
import qualified Data.Map                 as Map
import           Data.Maybe               (mapMaybe)
import qualified Data.Set                 as Set
import           GHC.Generics             (Generic)

import           Ledger.Blockchain
import           Plutus.V1.Ledger.Address (Address (..))
import           Plutus.V1.Ledger.Tx      (Tx (..), TxIn (..), TxOut (..), TxOutRef (..), TxOutTx (..), txId)
import qualified Plutus.V1.Ledger.Tx      as Tx
import           Plutus.V1.Ledger.Value   (Value)

type UtxoMap = Map TxOutRef TxOutTx

-- | A map of 'Address'es and their unspent outputs.
newtype AddressMap = AddressMap { getAddressMap :: Map Address UtxoMap }
    deriving stock (Show, Eq, Generic)
    deriving newtype (Serialise)

-- | An address map with a single unspent transaction output.
singleton :: (Address, TxOutRef, Tx, TxOut) -> AddressMap
singleton (addr, ref, tx, ot) = AddressMap $ Map.singleton addr (Map.singleton ref (TxOutTx tx ot))

outRefMap :: AddressMap -> Map TxOutRef TxOutTx
outRefMap (AddressMap am) = Map.unions (snd <$> Map.toList am)

-- | Filter the transaction output references in the map
filterRefs :: (TxOutRef -> TxOutTx -> Bool) -> AddressMap -> AddressMap
filterRefs flt =
    AddressMap . Map.map (Map.filterWithKey flt) . getAddressMap

-- NB: The ToJSON and FromJSON instance for AddressMap use the `Serialise`
-- instance with a base16 encoding, similar to the instances in Types.hs.
-- I chose this approach over the generic deriving mechanism because that would
-- have required `ToJSONKey` and `FromJSONKey` instances for `Address` and
-- `TxOutRef` which ultimately would have introduced more boilerplate code
-- than what we have here.

instance ToJSON AddressMap where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON AddressMap where
    parseJSON = JSON.decodeSerialise

instance Semigroup AddressMap where
    (AddressMap l) <> (AddressMap r) = AddressMap (Map.unionWith add l r) where
        add = Map.union

instance Monoid AddressMap where
    mappend = (<>)
    mempty = AddressMap Map.empty

type instance Index AddressMap = Address
type instance IxValue AddressMap = Map TxOutRef TxOutTx

instance Ixed AddressMap where
    ix adr f (AddressMap mp) = AddressMap <$> ix adr f mp

instance At AddressMap where
    at idx = lens g s where
        g (AddressMap mp) = mp ^. at idx
        s (AddressMap mp) utxo = AddressMap $ mp & at idx .~ utxo

-- | Get the funds available at a particular address.
fundsAt :: Address -> Lens' AddressMap UtxoMap
fundsAt addr = at addr . non mempty

-- | Add an address with no unspent outputs to a map. If the address already
--   exists, do nothing.
addAddress :: Address -> AddressMap -> AddressMap
addAddress adr (AddressMap mp) = AddressMap $ Map.alter upd adr mp where
    upd :: Maybe UtxoMap -> Maybe UtxoMap
    upd = maybe (Just Map.empty) Just

-- | Add a list of 'Address'es with no unspent outputs to the map.
addAddresses :: [Address] -> AddressMap -> AddressMap
addAddresses = flip (foldr addAddress)

-- | The total value of unspent outputs (which the map knows about) at an address.
values :: AddressMap -> Map Address Value
values = Map.map (fold . Map.map (txOutValue . txOutTxOut)) . getAddressMap

-- | Walk through the address map, applying an effectful function to each entry.
traverseWithKey ::
     Applicative f
  => (Address -> Map TxOutRef TxOutTx -> f (Map TxOutRef TxOutTx))
  -> AddressMap
  -> f AddressMap
traverseWithKey f (AddressMap m) = AddressMap <$> Map.traverseWithKey f m

-- | Create an 'AddressMap' with the unspent outputs of a single transaction.
fromTxOutputs :: Tx -> AddressMap
fromTxOutputs tx =
    AddressMap . Map.fromListWith Map.union . fmap mkUtxo . zip [0..] . txOutputs $ tx where
    mkUtxo (i, t) = (txOutAddress t, Map.singleton (TxOutRef h i) (TxOutTx tx t))
    h = txId tx

-- | Create a map of unspent transaction outputs to their addresses (the
-- "inverse" of an 'AddressMap', without the values)
knownAddresses :: AddressMap -> Map TxOutRef Address
knownAddresses = Map.fromList . unRef . Map.toList . getAddressMap where
    unRef :: [(Address, Map TxOutRef TxOutTx)] -> [(TxOutRef, Address)]
    unRef lst = do
        (a, outRefs) <- lst
        (rf, _) <- Map.toList outRefs
        pure (rf, a)

-- | Update an 'AddressMap' with the inputs and outputs of a new
-- transaction. @updateAddresses@ does /not/ add or remove any keys from the map.
updateAddresses :: Tx -> AddressMap -> AddressMap
updateAddresses tx utxo = AddressMap $ Map.mapWithKey upd (getAddressMap utxo) where
    -- adds the newly produced outputs, and removes the consumed outputs, for
    -- an address `adr`
    upd :: Address -> Map TxOutRef TxOutTx -> Map TxOutRef TxOutTx
    upd adr mp = Map.union (producedAt adr) mp `Map.difference` consumedFrom adr

    -- The TxOutRefs produced by the transaction, for a given address
    producedAt :: Address -> Map TxOutRef TxOutTx
    producedAt adr = Map.findWithDefault Map.empty adr outputs

    -- The TxOutRefs consumed by the transaction, for a given address
    consumedFrom :: Address -> Map TxOutRef ()
    consumedFrom adr = maybe Map.empty (Map.fromSet (const ())) $ Map.lookup adr consumedInputs

    AddressMap outputs = fromTxOutputs tx

    consumedInputs = inputs (knownAddresses utxo) tx

-- | Update an 'AddressMap' with the inputs and outputs of a new
-- transaction, including all addresses in the transaction.
updateAllAddresses :: Tx -> AddressMap -> AddressMap
-- updateAddresses handles getting rid of spent outputs, so all we have to do is add in the
-- new things. We can do this by just merging in `fromTxOutputs`, which will have many of the
-- things that are already there, but also the new things.
updateAllAddresses tx utxo = updateAddresses tx utxo <> fromTxOutputs tx

-- | The inputs consumed by a transaction, indexed by address.
inputs ::
    Map TxOutRef Address
    -- ^ A map of 'TxOutRef's to their 'Address'es
    -> Tx
    -> Map Address (Set.Set TxOutRef)
inputs addrs = Map.fromListWith Set.union
    . fmap (fmap Set.singleton . swap)
    . mapMaybe ((\a -> sequence (a, Map.lookup a addrs)) . txInRef)
    . Set.toList
    . view Tx.inputs

-- | Restrict an 'AddressMap' to a set of addresses.
restrict :: AddressMap -> Set.Set Address -> AddressMap
restrict (AddressMap mp) = AddressMap . Map.restrictKeys mp

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

-- | Get the set of all addresses that the transaction spends outputs from
--   or produces outputs to
addressesTouched :: AddressMap -> Tx -> Set.Set Address
addressesTouched utxo t = ins <> outs where
    ins = Map.keysSet (inputs (knownAddresses utxo) t)
    outs = Map.keysSet (getAddressMap (fromTxOutputs t))

-- | The unspent transaction outputs of the ledger as a whole.
fromChain :: Blockchain -> AddressMap
fromChain = foldr updateAllAddresses mempty . join
