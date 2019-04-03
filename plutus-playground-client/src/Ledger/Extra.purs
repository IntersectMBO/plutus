module Ledger.Extra where

import Prelude

import Data.Array as Array
import Data.Generic (class Generic, gShow)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple, fst)

newtype LedgerMap k v = LedgerMap (Array (Tuple k v))

derive instance genericLedgerMap :: (Generic k, Generic v) => Generic (LedgerMap k v)
derive instance newtypeLedgerMap :: Newtype (LedgerMap k v) _

instance eqLedgerMap :: (Ord k, Eq v) => Eq (LedgerMap k v) where
  eq (LedgerMap xs) (LedgerMap ys) =
    Array.sortWith fst xs == Array.sortWith fst ys

instance showValue :: (Generic k, Generic v, Show k, Show v) => Show (LedgerMap k v) where
  show = gShow


_LedgerMap :: forall k v. Lens' (LedgerMap k v) (Array (Tuple k v))
_LedgerMap = _Newtype
