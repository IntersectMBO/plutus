module Popper.Types where

import Prelude
import Control.Alt ((<|>))
import Data.Maybe (Maybe(..))
import Web.HTML (HTMLElement)

data Placement
  = Auto
  | AutoStart
  | AutoEnd
  | Top
  | TopStart
  | TopEnd
  | Bottom
  | BottomStart
  | BottomEnd
  | Right
  | RightStart
  | RightEnd
  | Left
  | LeftStart
  | LeftEnd

derive instance eqPlacement :: Eq Placement

data PositioningStrategy
  = Absolute
  | Fixed

type Rect
  = { width :: Number
    , height :: Number
    , x :: Number
    , y :: Number
    }

newtype Padding
  = Padding
  { top :: Maybe Number
  , left :: Maybe Number
  , right :: Maybe Number
  , bottom :: Maybe Number
  }

instance semigroupPadding :: Semigroup Padding where
  append (Padding fst) (Padding snd) =
    Padding
      { top: fst.top <|> snd.top
      , left: fst.left <|> snd.left
      , right: fst.right <|> snd.right
      , bottom: fst.bottom <|> snd.bottom
      }

instance monoidPadding :: Monoid Padding where
  mempty =
    Padding
      { top: Nothing, left: Nothing, right: Nothing, bottom: Nothing }

pAll :: Number -> Padding
pAll n = Padding { top: Just n, left: Just n, right: Just n, bottom: Just n }

pTop :: Number -> Padding
pTop top = Padding { top: Just top, left: Nothing, right: Nothing, bottom: Nothing }

pLeft :: Number -> Padding
pLeft left = Padding { top: Nothing, left: Just left, right: Nothing, bottom: Nothing }

pRight :: Number -> Padding
pRight right = Padding { top: Nothing, left: Nothing, right: Just right, bottom: Nothing }

pBottom :: Number -> Padding
pBottom bottom = Padding { top: Nothing, left: Nothing, right: Nothing, bottom: Just bottom }

type CalculateFromBoundingBox a
  = { popper :: Rect, reference :: Rect, placement :: Placement } -> a

type Offset
  = { skidding :: Number, distance :: Number }

data OffsetOption
  = OffsetValue Offset
  | OffsetFn (CalculateFromBoundingBox Offset)

data PaddingOption
  = PaddingValue Padding
  | PaddingFn (CalculateFromBoundingBox Padding)

data TetherOffsetOption
  = TetherOffset Number
  | TetherOffsetFn (CalculateFromBoundingBox Number)

data Boundary
  = ClippinParents
  | SingleElementBoundary HTMLElement
  | MultipleElementsBoundary (Array HTMLElement)

data RootBoundary
  = DocumentBoundary
  | ViewportBoundary

foreign import data Modifier :: Type

foreign import data PopperInstance :: Type

type Options
  = { placement :: Placement
    , modifiers :: Array Modifier
    , strategy :: PositioningStrategy
    -- , onFirstUpdate ::
    }

type ComputeStyleOptions
  = { gpuAcceleration :: Boolean
    , adaptive :: Boolean
    , roundOffsets :: Boolean
    }

type EventListenerOptions
  = { scroll :: Boolean
    , resize :: Boolean
    }

type PreventOverflowOptions
  = { mainAxis :: Boolean
    , altAxis :: Boolean
    , padding :: Padding
    , boundary :: Boundary
    , altBoundary :: Boolean
    , rootBoundary :: RootBoundary
    , tether :: Boolean
    , tetherOffset :: TetherOffsetOption
    }

type FlipOptions
  = { padding :: Padding
    , boundary :: Boundary
    , rootBoundary :: RootBoundary
    , flipVariations :: Boolean
    , allowedAutoPlacements :: Array Placement
    -- TODO: need to come up with a constructor for Placement or oppositePlacement
    -- fallbackPlacements: Array<Placement>, // [oppositePlacement]
    }
