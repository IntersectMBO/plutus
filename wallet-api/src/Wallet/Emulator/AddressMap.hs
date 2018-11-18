{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies    #-}
module Wallet.Emulator.AddressMap(
    AddressMap(..),
    addAddress,
    addAddresses,
    values,
    fromTxOutputs,
    knownAddresses,
    updateAddresses
    ) where

import           Data.Map            (Map)
import qualified Data.Map            as Map
import           Data.Maybe          (mapMaybe)
import           Data.Monoid         (Monoid (..), Sum (..))
import           Data.Semigroup      (Semigroup (..))
import qualified Data.Set            as Set
import           Lens.Micro          (lens, (&), (.~), (^.))
import           Lens.Micro.GHC      ()
import           Lens.Micro.Internal (At (..), Index, IxValue, Ixed (..))

import           Wallet.UTXO         (Address', Tx (..), TxIn (..), TxIn', TxOut (..), TxOutRef (..), TxOutRef', Value,
                                      hashTx)

-- | A map of [[Address']]es and their unspent outputs
newtype AddressMap = AddressMap { getAddressMap :: Map Address' (Map TxOutRef' Value) }
    deriving Show

instance Semigroup AddressMap where
    (AddressMap l) <> (AddressMap r) = AddressMap (Map.unionWith add l r) where
        add = Map.unionWith (+)

instance Monoid AddressMap where
    mappend = (<>)
    mempty = AddressMap Map.empty

type instance Index AddressMap = Address'
type instance IxValue AddressMap = Map TxOutRef' Value

instance Ixed AddressMap where
    ix adr f (AddressMap mp) = AddressMap <$> ix adr f mp

instance At AddressMap where
    at idx = lens g s where
        g (AddressMap mp) = mp ^. at idx
        s (AddressMap mp) utxo = AddressMap $ mp & at idx .~ utxo

-- | Add an address with no unspent outputs. If the address already exists, do
--   nothing.
addAddress :: Address' -> AddressMap -> AddressMap
addAddress adr (AddressMap mp) = AddressMap $ Map.alter upd adr mp where
    upd :: Maybe (Map TxOutRef' Value) -> Maybe (Map TxOutRef' Value)
    upd = maybe (Just Map.empty) Just

-- | Add a list of [[Address']]es with no unspent outputs
addAddresses :: [Address'] -> AddressMap -> AddressMap
addAddresses = flip (foldr addAddress)

-- | The total value of unspent outputs at an address
values :: AddressMap -> Map Address' Value
values = Map.map (getSum . foldMap Sum) . getAddressMap

-- | An [[AddressMap]] with the unspent outputs of a single transaction
fromTxOutputs :: Tx -> AddressMap
fromTxOutputs tx =
    AddressMap . Map.fromListWith Map.union . fmap mkUtxo . zip [0..] . txOutputs $ tx where
    mkUtxo (i, TxOut{..}) = (txOutAddress, Map.singleton (TxOutRef h i) txOutValue)
    h = hashTx tx

-- | A map of unspent transaction outputs to their addresses (the "inverse" of
--   [[AddressMap]], without the values
knownAddresses :: AddressMap -> Map TxOutRef' Address'
knownAddresses = Map.fromList . unRef . Map.toList . getAddressMap where
    unRef :: [(Address', Map TxOutRef' Value)] -> [(TxOutRef', Address')]
    unRef lst = do
        (a, outRefs) <- lst
        (rf, _) <- Map.toList outRefs
        pure (rf, a)

-- | Update the [[AddressMap]] with the inputs and outputs of a new
--   transaction. `updateAddresses` does not add or remove any keys from its
--   second argument.
updateAddresses :: Tx -> AddressMap -> AddressMap
updateAddresses tx utxo = AddressMap $ Map.mapWithKey upd (getAddressMap utxo) where
    -- adds the newly produced outputs, and removes the consumed outputs, for
    -- an address `adr`
    upd adr mp = Map.union (producedAt adr) mp `Map.difference` consumedFrom adr

    -- The TxOutRefs produced by the transaction, for a given address
    producedAt :: Address' -> Map TxOutRef' Value
    producedAt adr = Map.findWithDefault Map.empty adr outputs

    -- The TxOutRefs consumed by the transaction, for a given address
    consumedFrom :: Address' -> Map TxOutRef' ()
    consumedFrom adr = maybe Map.empty (Map.fromSet (const ())) $ Map.lookup adr consumedInputs

    consumedInputs = inputs (knownAddresses utxo) (Set.toList $ txInputs tx)

    AddressMap outputs = fromTxOutputs tx

-- Inputs consumed by the transaction, index by address.
inputs ::
    Map TxOutRef' Address'
    -- ^ A map of [[TxOutRef']]s to their [[Address']]es
    -> [TxIn']
    -> Map Address' (Set.Set TxOutRef')
inputs addrs = Map.fromListWith Set.union
    . fmap (fmap Set.singleton . swap)
    . mapMaybe ((\a -> sequence (a, Map.lookup a addrs)) . txInRef)

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)
