module Component.Label.View
  ( defaultInput
  , render
  , renderWithChildren
  ) where

import Prelude
import Component.Label.Types (Input, Variant(..))
import Halogen.Css (classNames)
import Halogen.HTML as HH

defaultInput :: Input
defaultInput =
  { for: ""
  , text: ""
  , variant: Nested
  }

render :: forall w action. Input -> HH.HTML w action
render params = renderWithChildren params pure

renderWithChildren ::
  forall w action.
  Input ->
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
