module Halogen.HTML.Extra (mapComponent) where

import Data.Bifunctor (bimap)
import Data.Functor (map)
import Halogen.HTML (ComponentHTML)

mapComponent :: forall m a b slots. (a -> b) -> ComponentHTML a slots m -> ComponentHTML b slots m
mapComponent f = bimap (map f) f
