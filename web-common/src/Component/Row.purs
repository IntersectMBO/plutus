module Component.Row
  ( Preset(..)
  , row
  , rowIn
  ) where

import Prologue
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
  | Between

instance defaultPreset :: Default Preset where
  default = Default

rowIn :: Preset -> LayoutOf
rowIn preset = layout $ [ "flex" ] <> baseClasses
  where
  baseClasses = case preset of
    NoSpace -> []
    Divided -> [ "divide-x-2", "divide-gray-300" ]
    Cramped -> [ "space-x-1" ]
    Snug -> [ "space-x-2" ]
    Default -> [ "space-x-4" ]
    Loose -> [ "space-x-6" ]
    Between -> [ "justify-between" ]

row :: Preset -> Layout
row preset = rowIn preset HH.div
