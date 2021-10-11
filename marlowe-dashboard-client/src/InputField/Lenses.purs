module InputField.Lenses
  ( _value
  , _pristine
  , _validator
  , _dropdownOpen
  , _dropdownLocked
  , _additionalCss
  , _id_
  , _placeholder
  , _readOnly
  , _valueOptions
  , _numberFormat
  , _after
  , _before
  ) where

import Prologue
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Symbol (SProxy(..))
import Halogen.HTML (HTML)
import InputField.Types (InputDisplayOptions, State)
import Marlowe.Extended.Metadata (NumberFormat)

_value :: forall e. Lens' (State e) String
_value = prop (SProxy :: SProxy "value")

_pristine :: forall e. Lens' (State e) Boolean
_pristine = prop (SProxy :: SProxy "pristine")

_validator :: forall e. Lens' (State e) (String -> Maybe e)
_validator = prop (SProxy :: SProxy "validator")

_dropdownOpen :: forall e. Lens' (State e) Boolean
_dropdownOpen = prop (SProxy :: SProxy "dropdownOpen")

_dropdownLocked :: forall e. Lens' (State e) Boolean
_dropdownLocked = prop (SProxy :: SProxy "dropdownLocked")

------------------------------------------------------------
_additionalCss :: forall w i. Lens' (InputDisplayOptions w i) (Array String)
_additionalCss = prop (SProxy :: SProxy "additionalCss")

_id_ :: forall w i. Lens' (InputDisplayOptions w i) String
_id_ = prop (SProxy :: SProxy "id_")

_placeholder :: forall w i. Lens' (InputDisplayOptions w i) String
_placeholder = prop (SProxy :: SProxy "placeholder")

_readOnly :: forall w i. Lens' (InputDisplayOptions w i) Boolean
_readOnly = prop (SProxy :: SProxy "readOnly")

_valueOptions :: forall w i. Lens' (InputDisplayOptions w i) (Array String)
_valueOptions = prop (SProxy :: SProxy "valueOptions")

_numberFormat :: forall w i. Lens' (InputDisplayOptions w i) (Maybe NumberFormat)
_numberFormat = prop (SProxy :: SProxy "numberFormat")

_after :: forall w i. Lens' (InputDisplayOptions w i) (Maybe (HTML w i))
_after = prop (SProxy :: SProxy "after")

_before :: forall w i. Lens' (InputDisplayOptions w i) (Maybe (HTML w i))
_before = prop (SProxy :: SProxy "before")
