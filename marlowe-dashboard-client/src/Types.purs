module Types
  ( AjaxResponse
  , DecodedAjaxResponse
  , WebData
  , DecodedWebData
  , DecodedAjaxError
  , CombinedWSStreamToServer(..)
  ) where

import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Foreign (MultipleErrors)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet) as Back
import Wallet.Types (ContractInstanceId) as Back

type AjaxResponse
  = Either AjaxError

type DecodedAjaxResponse
  = Either DecodedAjaxError

type WebData
  = RemoteData AjaxError

type DecodedWebData
  = RemoteData DecodedAjaxError

type DecodedAjaxError
  = Either AjaxError MultipleErrors

-- TODO: purescript-bridge generates a version of this type in Plutus.PAB.Webserver.Types, but the
-- encode/decode instances are wrong. I haven't figured out how to fix that yet, but in the
-- meantime this hack works. :/
data CombinedWSStreamToServer
  = Subscribe (Either Back.ContractInstanceId Back.Wallet)
  | Unsubscribe (Either Back.ContractInstanceId Back.Wallet)

derive instance genericCombinedWSStreamToServer :: Generic CombinedWSStreamToServer _

instance encodeCombinedWSStreamToServer :: Encode CombinedWSStreamToServer where
  encode value = genericEncode defaultOptions value

instance decodeCombinedWSStreamToServer :: Decode CombinedWSStreamToServer where
  decode value = genericDecode defaultOptions value
