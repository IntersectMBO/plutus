module Data.Void(module Data.Void) where
import MiniPrelude
import Prelude qualified ()

data Void

absurd :: forall a . Void -> a
absurd v = seq v (error "absurd")

vacuous :: forall f a . Functor f => f Void -> f a
vacuous = fmap absurd
