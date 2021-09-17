module Web.Common.Components.Label
  ( Params
  , Variant(..)
  , render
  , defaultParams
  ) where

import Prelude
import Data.Array (fromFoldable)
import Data.Maybe (Maybe(..))
import Halogen.Css (classNames)
import Halogen.HTML as HH

-------------------------------------------------------------------------------
-- Public API types
-------------------------------------------------------------------------------
data Variant
  = Above
  | Nested

type Params w i
  = { after :: Maybe (HH.HTML w i)
    , before :: Maybe (HH.HTML w i)
    , for :: String
    , text :: String
    , variant :: Variant
    }

-------------------------------------------------------------------------------
-- Public API
-------------------------------------------------------------------------------
defaultParams :: forall w i. Params w i
defaultParams =
  { after: Nothing
  , before: Nothing
  , for: ""
  , text: ""
  , variant: Nested
  }

render :: forall w i. Params w i -> HH.HTML w i
render params =
  HH.label
    ( [ classNames labelStyles ]
    )
    $ fromFoldable params.before
    <> [ HH.span [ classNames spanStyles ] [ HH.text params.text ] ]
    <> fromFoldable params.after
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
