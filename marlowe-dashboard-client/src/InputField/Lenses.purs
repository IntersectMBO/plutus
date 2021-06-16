module InputField.Lenses
  ( _value
  , _pristine
  , _validator
  , _dropdownOpen
  , _baseCss
  , _additionalCss
  , _id_
  , _placeholder
  , _readOnly
  , _datalistId
  , _valueOptions
  ) where

import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Symbol (SProxy(..))
import InputField.Types (InputDisplayOptions, State)

_value :: forall e. Lens' (State e) String
_value = prop (SProxy :: SProxy "value")

_pristine :: forall e. Lens' (State e) Boolean
_pristine = prop (SProxy :: SProxy "pristine")

_validator :: forall e. Lens' (State e) (String -> Maybe e)
_validator = prop (SProxy :: SProxy "validator")

_dropdownOpen :: forall e. Lens' (State e) Boolean
_dropdownOpen = prop (SProxy :: SProxy "dropdownOpen")

------------------------------------------------------------
_baseCss :: Lens' InputDisplayOptions (Boolean -> Array String)
_baseCss = prop (SProxy :: SProxy "baseCss")

_additionalCss :: Lens' InputDisplayOptions (Array String)
_additionalCss = prop (SProxy :: SProxy "additionalCss")

_id_ :: Lens' InputDisplayOptions String
_id_ = prop (SProxy :: SProxy "id_")

_placeholder :: Lens' InputDisplayOptions String
_placeholder = prop (SProxy :: SProxy "placeholder")

_readOnly :: Lens' InputDisplayOptions Boolean
_readOnly = prop (SProxy :: SProxy "readOnly")

_datalistId :: Lens' InputDisplayOptions (Maybe String)
_datalistId = prop (SProxy :: SProxy "datalistId")

_valueOptions :: Lens' InputDisplayOptions (Array String)
_valueOptions = prop (SProxy :: SProxy "valueOptions")
