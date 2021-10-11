module Component.Box
  ( Preset(..)
  , box
  , boxIn
  ) where

import Component.Container
  ( Container
  , ContainerOf
  , container
  )
import Data.Default (class Default)
import Halogen.HTML as HH

data Preset
  = NoSpace
  | Cramped
  | Snug
  | Default
  | Loose
  | CardCramped
  | CardSnug
  | Card
  | CardLoose

instance defaultPreset :: Default Preset where
  default = Default

boxIn :: Preset -> ContainerOf
boxIn preset = container baseClasses
  where
  baseClasses = case preset of
    NoSpace -> [ "p-0" ]
    Cramped -> [ "p-1" ]
    Snug -> [ "p-2" ]
    Default -> [ "p-4" ]
    Loose -> [ "p-6" ]
    CardCramped -> [ "p-1", "rounded-sm", "shadow-sm" ]
    CardSnug -> [ "p-2", "rounded", "shadow-sm" ]
    Card -> [ "p-4", "rounded", "shadow" ]
    CardLoose -> [ "p-6", "rounded-lg", "shadow-lg" ]

box :: Preset -> Container
box preset = boxIn preset HH.div
