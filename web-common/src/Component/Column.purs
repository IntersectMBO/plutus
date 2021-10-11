module Component.Column
  ( Preset(..)
  , column
  , columnIn
  ) where

import Component.Layout
  ( Layout
  , LayoutOf
  , layout
  )
import Data.Default (class Default)
import Halogen.HTML as HH

data Preset
  = NoSpace
  | Divided
  | Cramped
  | Snug
  | Default
  | Loose

instance defaultPreset :: Default Preset where
  default = Default

columnIn :: Preset -> LayoutOf
columnIn preset = layout baseClasses
  where
  baseClasses = case preset of
    NoSpace -> []
    Divided -> [ "divide-y-2", "divide-gray-300" ]
    Cramped -> [ "space-y-1" ]
    Snug -> [ "space-y-2" ]
    Default -> [ "space-y-4" ]
    Loose -> [ "space-y-6" ]

column :: Preset -> Layout
column preset = columnIn preset HH.div
