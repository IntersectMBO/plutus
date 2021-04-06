module Bridge
  ( _bridge
  , class Bridge
  , toFront
  , toBack
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Json.JsonUUID (JsonUUID(..))
import Data.Lens (Iso', iso)
import Data.Map (Map, fromFoldable, toUnfoldable) as Front
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Marlowe.Semantics (Assets(..), Slot(..)) as Front
import Network.RemoteData (RemoteData)
import Plutus.V1.Ledger.Crypto (PubKey(..)) as Back
import Plutus.V1.Ledger.Slot (Slot(..)) as Back
import Plutus.V1.Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..)) as Back
import PlutusTx.AssocMap (Map, fromTuples, toTuples) as Back
import Servant.PureScript.Ajax (AjaxError)
import Wallet.Emulator.Wallet (Wallet(..)) as Back
import Wallet.Types (ContractInstanceId(..)) as Back
import Wallet.Types (Payment)
import WalletData.Types (ContractInstanceId(..), Wallet(..)) as Front

-- | Servant.PureScript generates PureScript types from the Haskell codebase with JSON encode and decode instances
--   that in principle enable easy communication between the (frontend) PureScript and (backend) Haskell code.
--   **However**:
--     - The Haskell code uses the newtype record shorthand a lot (e.g. newtype Slot = { getSlot: Integer }),
--       which PureScript takes literally. Using these types directly in the PureScript code thus leads to a
--       lot of tedious boilerplate.
--     - The PureScript Marlowe.Semantics modules uses aliases in a handful of places where the Haskell code uses
--       newtypes. I don't know why this is (it was before my time), and we should look into bringing things into
--       closer alignment. But in the meantime, this module plasters over the cracks.
--     - The Haskell code uses a custom `PlutusTx.AssocMap` where the PureScript code uses the standard `Data.Map`.
--       This is because the Plutus core cannot compile the standard Haskell `Data.Map`.
--
-- TODO: Bring the PureScript Marlowe.Semantics types into closer alignment with their Haskell equivalents.
--
-- TODO: Some form of "bridge" module like this will probably always be wanted, even with the types in closer
-- alignment. But it should be as general as possible and moved into a web-common directory.
_bridge :: forall a b. Bridge a b => Iso' a b
_bridge = iso toFront toBack

class Bridge a b where
  toFront :: a -> b
  toBack :: b -> a

instance webDataBridge :: (Bridge a b) => Bridge (RemoteData AjaxError a) (RemoteData AjaxError b) where
  toFront = map toFront
  toBack = map toBack

instance tupleBridge :: (Bridge a c, Bridge b d) => Bridge (Tuple a b) (Tuple c d) where
  toFront (a /\ b) = toFront a /\ toFront b
  toBack (c /\ d) = toBack c /\ toBack d

instance jsonTupleBridge :: (Bridge a c, Bridge b d) => Bridge (JsonTuple a b) (JsonTuple c d) where
  toFront (JsonTuple tuple) = JsonTuple $ toFront tuple
  toBack (JsonTuple tuple) = JsonTuple $ toBack tuple

instance mapBridge :: (Ord a, Ord c, Bridge a c, Bridge b d) => Bridge (Back.Map a b) (Front.Map c d) where
  toFront map = Front.fromFoldable $ toFront <$> Back.toTuples map
  toBack map = Back.fromTuples $ toBack <$> Front.toUnfoldable map

instance slotBridge :: Bridge Back.Slot Front.Slot where
  toFront slot@(Back.Slot { getSlot }) = Front.Slot getSlot
  toBack (Front.Slot slot) = Back.Slot { getSlot: slot }

instance bigIntegerBridge :: Bridge BigInteger BigInteger where
  toFront = identity
  toBack = identity

-- FIXME: Marlowe.Semantics.PubKey is currently just an alias for String
instance pubKeyBridge :: Bridge Back.PubKey String where
  toFront (Back.PubKey { getPubKey }) = getPubKey
  toBack getPubKey = Back.PubKey { getPubKey }

-- FIXME: the Haskell type is called 'Value' but the PureScript type is called 'Assets'
instance valueBridge :: Bridge Back.Value Front.Assets where
  toFront (Back.Value { getValue }) = Front.Assets $ toFront getValue
  toBack (Front.Assets getValue) = Back.Value { getValue: toBack getValue }

-- FIXME: Marlowe.Semantics.TokenName is currently just an alias for String
instance tokenNameBridge :: Bridge Back.TokenName String where
  toFront (Back.TokenName { unTokenName }) = unTokenName
  toBack unTokenName = Back.TokenName { unTokenName }

-- FIXME: Marlowe.Semantics.CurrencySymbol is currently just an alias for String
instance currencySymbolBridge :: Bridge Back.CurrencySymbol String where
  toFront (Back.CurrencySymbol { unCurrencySymbol }) = unCurrencySymbol
  toBack unCurrencySymbol = Back.CurrencySymbol { unCurrencySymbol }

instance walletBridge :: Bridge Back.Wallet Front.Wallet where
  toFront (Back.Wallet { getWallet }) = Front.Wallet getWallet
  toBack (Front.Wallet getWallet) = Back.Wallet { getWallet }

instance contractInstanceIdBridge :: Bridge Back.ContractInstanceId Front.ContractInstanceId where
  toFront (Back.ContractInstanceId { unContractInstanceId: JsonUUID uuid }) = Front.ContractInstanceId uuid
  toBack (Front.ContractInstanceId uuid) = Back.ContractInstanceId { unContractInstanceId: JsonUUID uuid }

-- NOTE: the `Payment` type defined in `Marlowe.Semantics` is for something different
instance paymentBridge :: Bridge Payment Payment where
  toFront = identity
  toBack = identity
