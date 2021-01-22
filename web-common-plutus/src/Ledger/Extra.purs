module Ledger.Extra where

import Data.Lens (Lens', lens, view)
import Data.Lens.Record (prop)
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Language.PlutusTx.AssocMap (unionWith)
import Language.PlutusTx.AssocMap as AssocMap
import Plutus.V1.Ledger.Ada (Ada(..))
import Plutus.V1.Ledger.Interval (Extended(..), Interval, LowerBound(..), UpperBound(..), _Interval)
import Plutus.V1.Ledger.Slot (Slot(..))
import Plutus.V1.Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Prelude (show, (+), (<<<), (<>))

humaniseInterval :: Interval Slot -> String
humaniseInterval interval = case from, to of
  LowerBound NegInf true, UpperBound PosInf true -> "All time"
  _, _ -> "From " <> humaniseSlot from <> " to " <> humaniseSlot to
  where
  from = view (_Interval <<< _ivFrom) interval

  to = view (_Interval <<< _ivTo) interval

humaniseSlot :: forall a. HasBound a Slot => a -> String
humaniseSlot bound = start <> " " <> end
  where
  start = case hasBound bound of
    NegInf -> "the start of time"
    Finite (Slot slot) -> "Slot " <> show slot.getSlot
    PosInf -> "the end of time"

  end = case isInclusive bound of
    true -> "(inclusive)"
    false -> "(exclusive)"

-- | Any type that contains an `Extended a` value and an inclusive/exclusive flag.
class HasBound a v | a -> v where
  hasBound :: a -> Extended v
  isInclusive :: a -> Boolean

instance lowerBoundHasBound :: HasBound (LowerBound v) v where
  hasBound (LowerBound x _) = x
  isInclusive (LowerBound _ x) = x

instance upperBoundHasBound :: HasBound (UpperBound v) v where
  hasBound (UpperBound x _) = x
  isInclusive (UpperBound _ x) = x

------------------------------------------------------------
_ivFrom :: forall a r. Lens' { ivFrom :: a | r } a
_ivFrom = prop (SProxy :: SProxy "ivFrom")

_ivTo :: forall a r. Lens' { ivTo :: a | r } a
_ivTo = prop (SProxy :: SProxy "ivTo")

_LowerBoundExtended :: forall a. Lens' (LowerBound a) (Extended a)
_LowerBoundExtended = lens get set
  where
  get (LowerBound e _) = e

  set (LowerBound _ i) e = LowerBound e i

_LowerBoundInclusive :: forall a. Lens' (LowerBound a) Boolean
_LowerBoundInclusive = lens get set
  where
  get (LowerBound _ i) = i

  set (LowerBound e _) i = LowerBound e i

_UpperBoundExtended :: forall a. Lens' (UpperBound a) (Extended a)
_UpperBoundExtended = lens get set
  where
  get (UpperBound e _) = e

  set (UpperBound _ i) e = UpperBound e i

_UpperBoundInclusive :: forall a. Lens' (UpperBound a) Boolean
_UpperBoundInclusive = lens get set
  where
  get (UpperBound _ i) = i

  set (UpperBound e _) i = UpperBound e i

_a :: forall a r. Lens' { a :: a | r } a
_a = prop (SProxy :: SProxy "a")

------------------------------------------------------------
sum :: Value -> Value -> Value
sum (Value { getValue: x }) (Value { getValue: y }) = Value { getValue: unionWith (unionWith (+)) x y }

adaToValue :: Ada -> Value
adaToValue (Lovelace ada) =
  Value
    { getValue:
        AssocMap.Map
          [ JsonTuple
              ( Tuple
                  (CurrencySymbol { unCurrencySymbol: "" })
                  (AssocMap.Map [ JsonTuple (Tuple (TokenName { unTokenName: "" }) ada.getLovelace) ])
              )
          ]
    }
