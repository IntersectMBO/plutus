module Popper.Internal
  ( createPopper -- constructor
  -- instance methods
  , forceUpdate
  , destroyPopper
  -- Modifiers
  , arrow
  , popperOffsets
  , computeStyles
  , applyStyles
  , eventListeners
  , offset
  , preventOverflow
  , flipPlacement
  ) where

import Prelude
import Data.Array as Array
import Data.Function.Uncurried (Fn0, Fn1, Fn2, runFn0, runFn1, runFn2)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception.Unsafe (unsafeThrow)
import Effect.Uncurried (EffectFn1, EffectFn3, runEffectFn1, runEffectFn3)
import Foreign (Foreign, unsafeToForeign)
import Foreign.Generic (encode) as Foreign
import Foreign.Object as Object
import Popper.Types (Boundary(..), ComputeStyleOptions, EventListenerOptions, Modifier, Offset, OffsetOption(..), Options, Padding(..), PaddingOption(..), Placement(..), PopperInstance, PositioningStrategy(..), PreventOverflowOptions, Rect, RootBoundary(..), TetherOffsetOption(..), FlipOptions)
import Web.HTML (HTMLElement)

-------------------------------------------------------------------------------------------------------
-- General note on Modifiers:
-- PopperJS has a plugin architecture around modifiers. We offer FFI bindings to them using the
-- "plain" uncurried helpers.
-- There is no need to use the effect uncurried functions (death man last words) as we treat Modifiers
-- as opaque types. We don't compare them, and have no need for referential transparency with them.
-- Some of the modifiers don't receive any parameters (e.g. applyStyles), but they are still functions
-- of no argument. This helps the bundler to tree shake the modifiers we don't use.
----
foreign import _arrow :: Fn2 HTMLElement Foreign Modifier

arrow :: HTMLElement -> PaddingOption -> Modifier
arrow elm (PaddingValue padding) = runFn2 _arrow elm (paddingToFFI padding)

arrow elm (PaddingFn fn) = runFn2 _arrow elm $ unsafeToForeign (paddingToFFI <<< fn <<< optsFromFFI)

foreign import _popperOffsets :: Fn0 Modifier

popperOffsets :: Modifier
popperOffsets = runFn0 _popperOffsets

foreign import _computeStyles :: Fn1 ComputeStyleOptions Modifier

computeStyles :: ComputeStyleOptions -> Modifier
computeStyles = runFn1 _computeStyles

foreign import _applyStyles :: Fn0 Modifier

applyStyles :: Modifier
applyStyles = runFn0 _applyStyles

foreign import _eventListeners :: Fn1 EventListenerOptions Modifier

eventListeners :: EventListenerOptions -> Modifier
eventListeners = runFn1 _eventListeners

foreign import _offset :: Fn1 Foreign Modifier

offset :: OffsetOption -> Modifier
offset (OffsetValue value) = runFn1 _offset $ unsafeToForeign { offset: offsetToFFI value }

offset (OffsetFn fn) = runFn1 _offset $ unsafeToForeign { offset: (offsetToFFI <<< fn <<< optsFromFFI) }

foreign import _preventOverflow :: Fn1 Foreign Modifier

preventOverflow :: PreventOverflowOptions -> Modifier
preventOverflow { mainAxis
, altAxis
, padding
, boundary
, altBoundary
, rootBoundary
, tether
, tetherOffset
} =
  runFn1 _preventOverflow
    $ Foreign.encode
        { mainAxis
        , altAxis
        , padding: paddingToFFI padding
        , boundary: boundaryToFFI boundary
        , altBoundary
        , rootBoundary: rootBoundaryToFFI rootBoundary
        , tether
        , tetherOffset: tetherOffsetToFFI tetherOffset
        }

foreign import _flipPlacement :: Fn1 Foreign Modifier

flipPlacement :: FlipOptions -> Modifier
flipPlacement { padding
, boundary
, rootBoundary
, flipVariations
, allowedAutoPlacements
} =
  runFn1 _flipPlacement
    $ Foreign.encode
        { padding: paddingToFFI padding
        , boundary: boundaryToFFI boundary
        , rootBoundary: rootBoundaryToFFI rootBoundary
        , flipVariations
        , allowedAutoPlacements: placementToFFI <$> allowedAutoPlacements
        }

--------------------------------------------------------------------------------
foreign import _createPopper :: EffectFn3 HTMLElement HTMLElement FFIOptions PopperInstance

createPopper :: HTMLElement -> HTMLElement -> Options -> Effect PopperInstance
createPopper reference popper options = runEffectFn3 _createPopper reference popper (optionsToFFI options)

foreign import _forceUpdate :: EffectFn1 PopperInstance Unit

forceUpdate :: PopperInstance -> Effect Unit
forceUpdate = runEffectFn1 _forceUpdate

foreign import _destroyPopper :: EffectFn1 PopperInstance Unit

destroyPopper :: PopperInstance -> Effect Unit
destroyPopper = runEffectFn1 _destroyPopper

--------------------------------------------------------------------------------
type FFIOptions
  = { placement :: String
    , modifiers :: Array Modifier
    , strategy :: String
    -- , onFirstUpdate ::
    }

optionsToFFI :: Options -> FFIOptions
optionsToFFI { placement, modifiers, strategy } =
  { placement: placementToFFI placement
  , modifiers
  , strategy: strategyToFFI strategy
  }

paddingToFFI :: Padding -> Foreign
paddingToFFI (Padding { top, left, right, bottom }) =
  Foreign.encode
    $ Object.fromFoldable
    $ Array.catMaybes
        [ Tuple "top" <$> top
        , Tuple "left" <$> left
        , Tuple "right" <$> right
        , Tuple "bottom" <$> bottom
        ]

boundaryToFFI :: Boundary -> Foreign
boundaryToFFI = case _ of
  ClippinParents -> unsafeToForeign "clippingParents"
  SingleElementBoundary elm -> unsafeToForeign elm
  MultipleElementsBoundary elems -> unsafeToForeign elems

rootBoundaryToFFI :: RootBoundary -> String
rootBoundaryToFFI = case _ of
  DocumentBoundary -> "document"
  ViewportBoundary -> "viewport"

offsetToFFI :: Offset -> Foreign
offsetToFFI { skidding, distance } = Foreign.encode [ skidding, distance ]

tetherOffsetToFFI :: TetherOffsetOption -> Foreign
tetherOffsetToFFI = case _ of
  TetherOffset n -> unsafeToForeign n
  TetherOffsetFn fn -> unsafeToForeign (fn <<< optsFromFFI)

placementToFFI :: Placement -> String
placementToFFI = case _ of
  Auto -> "auto"
  AutoStart -> "auto-start"
  AutoEnd -> "auto-end"
  Top -> "top"
  TopStart -> "top-start"
  TopEnd -> "top-end"
  Bottom -> "bottom"
  BottomStart -> "bottom-start"
  BottomEnd -> "bottom-end"
  Right -> "right"
  RightStart -> "right-start"
  RightEnd -> "right-end"
  Left -> "left"
  LeftStart -> "left-start"
  LeftEnd -> "left-end"

optsFromFFI :: { popper :: Rect, reference :: Rect, placement :: String } -> { popper :: Rect, reference :: Rect, placement :: Placement }
optsFromFFI { popper, reference, placement } = { popper, reference, placement: unsafePlacementFromFFI placement }

unsafePlacementFromFFI :: String -> Placement
unsafePlacementFromFFI = case _ of
  "auto" -> Auto
  "auto-start" -> AutoStart
  "auto-end" -> AutoEnd
  "top" -> Top
  "top-start" -> TopStart
  "top-end" -> TopEnd
  "bottom" -> Bottom
  "bottom-start" -> BottomStart
  "bottom-end" -> BottomEnd
  "right" -> Right
  "right-start" -> RightStart
  "right-end" -> RightEnd
  "left" -> Left
  "left-start" -> LeftStart
  "left-end" -> LeftEnd
  str -> unsafeThrow $ "Popper.js internal: Invalid placement string: " <> str

strategyToFFI :: PositioningStrategy -> String
strategyToFFI = case _ of
  Absolute -> "absolute"
  Fixed -> "fixed"
