module InputField.Lenses
  ( _value
  , _pristine
  , _validator
  , _baseCss
  , _additionalCss
  , _id_
  , _placeholder
  , _readOnly
  , _datalistId
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
