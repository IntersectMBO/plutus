module Bridge
  ( class Bridge
  , toFront
  , toBack
  , contractInstanceIdFromString
  ) where

import Prelude
import Data.BigInteger (BigInteger)
import Data.Json.JsonUUID (JsonUUID(..))
import Data.Lens (Iso', iso)
import Data.Map (Map, fromFoldable, toUnfoldable) as Front
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Data.UUID (parseUUID)
import Marlowe.Semantics (Assets(..), Slot(..)) as Front
import Plutus.V1.Ledger.Crypto (PubKey(..)) as Back
import Plutus.V1.Ledger.Slot (Slot(..)) as Back
import Plutus.V1.Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..)) as Back
import PlutusTx.AssocMap (Map, fromTuples, toTuples) as Back
import Wallet.Emulator.Wallet (Wallet) as Back
import Wallet.Types (ContractInstanceId(..))

_bridge :: forall a b. Bridge a b => Iso' a b
_bridge = iso toFront toBack

class Bridge a b where
  toFront :: a -> b
  toBack :: b -> a

instance tupleBridge :: (Bridge a c, Bridge b d) => Bridge (Tuple a b) (Tuple c d) where
  toFront (a /\ b) = toFront a /\ toFront b
  toBack (c /\ d) = toBack c /\ toBack d

instance mapBridge :: (Ord a, Ord c, Bridge a c, Bridge b d) => Bridge (Back.Map a b) (Front.Map c d) where
  toFront map = Front.fromFoldable $ toFront <$> Back.toTuples map
  toBack map = Back.fromTuples $ toBack <$> Front.toUnfoldable map

instance slotBridge :: Bridge Back.Slot Front.Slot where
  toFront slot@(Back.Slot { getSlot }) = Front.Slot getSlot
  toBack (Front.Slot slot) = Back.Slot { getSlot: slot }

instance bigIntegerBridge :: Bridge BigInteger BigInteger where
  toFront a = a
  toBack a = a

-- Marlowe.Semantics.PubKey is currently just an alias for String
instance pubKeyBridge :: Bridge Back.PubKey String where
  toFront (Back.PubKey { getPubKey }) = getPubKey
  toBack getPubKey = Back.PubKey { getPubKey }

instance valueBridge :: Bridge Back.Value Front.Assets where
  toFront (Back.Value { getValue }) = Front.Assets $ toFront getValue
  toBack (Front.Assets getValue) = Back.Value $ { getValue: toBack getValue }

-- Marlowe.Semantics.TokenName is currently just an alias for String
instance tokenNameBridge :: Bridge Back.TokenName String where
  toFront (Back.TokenName { unTokenName }) = unTokenName
  toBack unTokenName = Back.TokenName { unTokenName }

-- Marlowe.Semantics.CurrencySymbol is currently just an alias for String
instance currencySymbolBridge :: Bridge Back.CurrencySymbol String where
  toFront (Back.CurrencySymbol { unCurrencySymbol }) = unCurrencySymbol
  toBack unCurrencySymbol = Back.CurrencySymbol { unCurrencySymbol }

--instance walletBridge :: Bridge Back.Wallet Front.Wallet
contractInstanceIdFromString :: String -> Maybe ContractInstanceId
contractInstanceIdFromString contractInstanceIdString = case parseUUID contractInstanceIdString of
  Just uuid -> Just $ ContractInstanceId { unContractInstanceId: JsonUUID uuid }
  _ -> Nothing
