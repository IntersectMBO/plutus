{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE TemplateHaskell #-}
module Cardano.Constitution.Config.Predicate.Types
    ( PredName (..)
    , PredValue
    , PredMeaning
    , PredMeaningApplied
    ) where

import PlutusPrelude (lowerInitialChar)
import PlutusTx as Tx (makeLift)
import PlutusTx.Eq qualified as Tx

import Data.Aeson as Aeson
import GHC.Generics
import Language.Haskell.TH.Syntax as TH (Lift)
import Prelude qualified as Haskell

-- | Unresolved predicate name, as read from JSON
data PredName =
    MinValue
  | MaxValue
  deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show, TH.Lift, Generic)
  deriving anyclass (Aeson.FromJSON)

-- | Unresolved predicate value, as read from JSON
type PredValue = Haskell.Integer

instance Tx.Eq PredName where
    {-# INLINABLE (==) #-}
    MinValue == MinValue = Haskell.True
    MaxValue == MaxValue = Haskell.True
    MinValue == _               = Haskell.False
    MaxValue == _               = Haskell.False

-- NOTE: needs manual instance for some reason;
-- a `deriving anyclass FromJSONKey` derived a problematic instance
instance Aeson.FromJSONKey PredName where
  fromJSONKey = genericFromJSONKey (defaultJSONKeyOptions { keyModifier = lowerInitialChar })

-- NOTE: **BE CAREFUL** of the ordering. Expected value is first arg, Proposed Value is second arg

-- | The "meaning" of a predicate, resolved from a `PredName` (a string in JSON)
-- to a Tx binary predicate function.
type PredMeaning = PredValue -- ^ the expected value, supplied from the config (json)
                 -> PredValue -- ^ the proposed value, taken from the ScriptContext
                 -> Haskell.Bool -- ^ True means the proposed value meets the expectations.

-- | The `PredMeaning` partially-applied to the expected `PredValue` (as read from JSON config)
type PredMeaningApplied = PredValue -- ^ the proposed value, taken from the ScriptContext
                        -> Haskell.Bool -- ^ True means the proposed value meets the expectations.

Tx.makeLift ''PredName
