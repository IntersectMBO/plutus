-- | A custom prelude that re-exports the most commonly implorted modules.
module Prologue
  ( module Prelude
  , module Data.Either
  , module Data.Generic.Rep
  , module Data.Lens
  , module Data.Maybe
  , module Data.Newtype
  , module Data.Symbol
  , module Data.Tuple
  , module Effect
  , module Effect.Aff
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Lens
  ( Lens'
  , _1
  , _2
  , _Just
  , _Left
  , _Nothing
  , _Right
  , assign
  , assignJust
  , preview
  , previewOn
  , set
  , setJust
  , traversed
  , use
  , view
  , viewOn
  , (%=)
  , (%~)
  , (&&=)
  , (&&~)
  , (*=)
  , (*~)
  , (++=)
  , (++~)
  , (+=)
  , (+~)
  , (-=)
  , (-~)
  , (.=)
  , (.~)
  , (//=)
  , (//~)
  , (<>=)
  , (<>~)
  , (?=)
  , (?~)
  , (^.)
  , (^..)
  , (^?)
  , (||=)
  , (||~)
  )
import Data.Maybe (Maybe(..))
import Data.Newtype
  ( class Newtype
  , over
  , un
  , under
  , unwrap
  , wrap
  )
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..), fst, snd)
import Effect (Effect)
import Effect.Aff (Aff)
