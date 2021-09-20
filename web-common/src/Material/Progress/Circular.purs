module Material.Progress.Circular where

import Prelude
import Data.Int (toNumber)
import Halogen.Css as HC
import Halogen.HTML as HH
import Halogen.SVG as HS
import Material.Progress (Progress(..), progressClass)

type Spec
  = { color :: String
    , width :: String
    , height :: String
    , additionalCss :: Array String
    , value :: Progress
    , trackWidth :: Int
    }

defaultSpec :: Spec
defaultSpec =
  { color: "text-black"
  , width: "w-8"
  , height: "h-8"
  , additionalCss: []
  , value: Indeterminate
  , trackWidth: 4
  }

view :: forall p a. Spec -> HH.HTML p a
view { color, width, height, additionalCss, value, trackWidth } =
  HH.div
    [ HC.classNames
        $ [ "progress"
          , "progress-circular"
          , progressClass value
          , color
          , width
          , height
          ]
        <> additionalCss
    ]
    [ HS.svg [ HS.viewBox $ HS.Box { height: 48, width: 48, x: 0, y: 0 } ]
        [ HS.circle
            [ HS.cx $ HS.Length 24.0
            , HS.cy $ HS.Length 24.0
            , HS.r $ HS.Length $ 24.0 - toNumber trackWidth * 2.0
            , HS.strokeWidth trackWidth
            ]
            []
        ]
    ]
