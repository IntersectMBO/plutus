module Web.Common.Components.Label
  ( Params
  , Variant(..)
  , defaultParams
  , render
  , renderWithChildren
  ) where

import Prelude
import Halogen.Css (classNames)
import Halogen.HTML as HH

-------------------------------------------------------------------------------
-- Public API types
-------------------------------------------------------------------------------
data Variant
  = Above
  | Nested

type Params
  = { for :: String
    , text :: String
    , variant :: Variant
    }

-------------------------------------------------------------------------------
-- Public API
-------------------------------------------------------------------------------
defaultParams :: Params
defaultParams =
  { for: ""
  , text: ""
  , variant: Nested
  }

render :: forall w action. Params -> HH.HTML w action
render params = renderWithChildren params pure

renderWithChildren ::
  forall w action.
  Params ->
  (HH.HTML w action -> Array (HH.HTML w action)) ->
  HH.HTML w action
renderWithChildren params renderChildren =
  HH.label
    ( [ classNames labelStyles ]
    )
    $ renderChildren
    $ HH.span [ classNames spanStyles ] [ HH.text params.text ]
  where
  labelStyles =
    [ "space-x-2", "leading-none" ]
      <> case params.variant of
          Above -> [ "block" ]
          Nested ->
            [ "absolute"
            , "z-10"
            , "left-2"
            , "-top-2.5"
            , "px-2"
            , "bg-white"
            ]

  spanStyles =
    [ "font-semibold" ]
      <> case params.variant of
          Above -> [ "text-sm" ]
          Nested -> [ "text-xs" ]
