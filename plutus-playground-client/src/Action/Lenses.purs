module Actions.Lenses
  ( _caller
  , _blocks
  , _InSlot
  , _slot
  ) where

import Data.BigInteger (BigInteger)
import Data.Lens (Iso', Lens', iso)
import Data.Lens.Record (prop)
import Data.Newtype (unwrap, wrap)
import Data.Symbol (SProxy(..))
import Plutus.V1.Ledger.Slot (Slot)
import Prelude ((<<<))

_caller :: forall r a. Lens' { caller :: a | r } a
_caller = prop (SProxy :: SProxy "caller")

_blocks :: forall r a. Lens' { blocks :: a | r } a
_blocks = prop (SProxy :: SProxy "blocks")

_InSlot :: Iso' Slot BigInteger
_InSlot = iso (_.getSlot <<< unwrap) (wrap <<< { getSlot: _ })

_slot :: forall r a. Lens' { slot :: a | r } a
_slot = prop (SProxy :: SProxy "slot")
