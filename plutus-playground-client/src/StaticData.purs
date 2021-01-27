module StaticData
  ( mkContractDemos
  , lookupContractDemo
  , bufferLocalStorageKey
  , keybindingsLocalStorageKey
  ) where

import Data.Array as Array
import Data.Lens (Lens', view)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import Data.Traversable (class Foldable)
import Foreign (F)
import Foreign.Generic (decodeJSON)
import LocalStorage (Key(..))
import Playground.Types (ContractDemo)
import Playground.Usecases (contractDemos)
import Prelude ((<<<), (==))

mkContractDemos :: F (Array ContractDemo)
mkContractDemos = do
  decodeJSON contractDemos

lookupContractDemo :: forall f. Foldable f => String -> f ContractDemo -> Maybe ContractDemo
lookupContractDemo key = Array.find (\demo -> view _contractDemoName demo == key)

_contractDemoName :: Lens' ContractDemo String
_contractDemoName = _Newtype <<< prop (SProxy :: SProxy "contractDemoName")

bufferLocalStorageKey :: Key
bufferLocalStorageKey = Key "PlutusPlaygroundBuffer"

keybindingsLocalStorageKey :: Key
keybindingsLocalStorageKey = Key "EditorPreferences.KeyBindings"
