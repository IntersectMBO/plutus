module StaticData
  ( mkContractDemos
  , lookup
  , _contractDemoName
  , _contractDemoEditorContents
  , bufferLocalStorageKey
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
import Language.Haskell.Interpreter (SourceCode)
import LocalStorage as LocalStorage
import Playground.Types (ContractDemo)
import Playground.Usecases as Usecases
import Prelude ((<<<), (==))

mkContractDemos :: F (Array ContractDemo)
mkContractDemos = do
  decodeJSON Usecases.contractDemos

_contractDemoName :: Lens' ContractDemo String
_contractDemoName = _Newtype <<< prop (SProxy :: SProxy "contractDemoName")

_contractDemoEditorContents :: Lens' ContractDemo SourceCode
_contractDemoEditorContents = _Newtype <<< prop (SProxy :: SProxy "contractDemoEditorContents")

lookup :: forall f. Foldable f => String -> f ContractDemo -> Maybe ContractDemo
lookup key = Array.find (\demo -> view _contractDemoName demo == key)

bufferLocalStorageKey :: LocalStorage.Key
bufferLocalStorageKey = LocalStorage.Key "PlutusPlaygroundBuffer"
