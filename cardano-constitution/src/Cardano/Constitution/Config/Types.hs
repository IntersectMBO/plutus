{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
-- editorconfig-checker-disable-file
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Cardano.Constitution.Config.Types
  ( PredKey (..)
  , Predicate
  , Predicates (..)
  , PredMeaning
  , Param
  , ParamKey
  , ParamValue (..)
  , ConstitutionConfig (..)
  ) where

import GHC.Generics
import Language.Haskell.TH.Syntax as TH
import PlutusTx.Eq as Tx
import PlutusTx.Ord as Tx
import PlutusTx.Ratio as Tx
import Prelude qualified as Haskell

{-| The "unresolved" Predicate names, as read from JSON. At runtime, these PredKeys
will each be resolved to actual `PredMeaning` functions. -}
data PredKey
  = MinValue
  | MaxValue
  | NotEqual
  deriving stock
    (Haskell.Eq, Haskell.Ord, Haskell.Show, Haskell.Enum, Haskell.Bounded, Generic, TH.Lift)

instance Tx.Eq PredKey where
  {-# INLINEABLE (==) #-}
  -- See Note [No catch-all]
  MinValue == MinValue = Haskell.True
  MaxValue == MaxValue = Haskell.True
  NotEqual == NotEqual = Haskell.True
  MinValue == _ = Haskell.False
  MaxValue == _ = Haskell.False
  NotEqual == _ = Haskell.False

-- | Polymorphic over the values. In reality, the value v is an Tx.Integer or Tx.Rational
type Predicate v = (PredKey, [v])

-- | newtype so we can overload FromJSON
newtype Predicates v = Predicates {unPredicates :: [Predicate v]}
  deriving stock (TH.Lift)
  deriving newtype (Haskell.Eq, Haskell.Show)

{-| The "meaning" of a predicate, resolved from a `PredKey` (a string in JSON)
to a Tx binary predicate function. -}
type PredMeaning a =
  Tx.Ord a
  => a
  -- ^ the expected value, supplied from the config (json)
  -> a
  -- ^ the proposed value, taken from the ScriptContext
  -> Haskell.Bool
  -- ^ True means the proposed value meets the expectations.

-- | Promised to be a stable identifier (stable at least for a whole cardano era)
type ParamKey = Haskell.Integer

data ParamValue
  = ParamInteger (Predicates Haskell.Integer)
  | ParamRational (Predicates Tx.Rational)
  | ParamList [ParamValue]
  | ParamAny
  | -- | An optional (`Maybe`-like) parameter value. See Note [Optional parameter values]
    ParamMaybe ParamValue
  deriving stock (Haskell.Eq, Haskell.Show, TH.Lift)

{- Note [Optional parameter values]

Some protocol parameters have an optional value on the ledger side (e.g. a `StrictMaybe Word32`).
The ledger encodes such a proposed value as `BuiltinData` using the same encoding
as PlutusTx's `Maybe` (and as the ledger's own `StrictMaybe`):

- `Constr 1 []`  : the proposal un-sets the parameter (`Nothing`)
- `Constr 0 [v]` : the proposal sets the parameter to `v` (`Just v`)

A `ParamMaybe inner` config value accepts the first form unconditionally
(no predicates can be meaningfully applied to an absent value), and validates `v` against
`inner` in the second form. Any other encoding is rejected.

This is different from a parameter being altogether absent from a proposal:
that is already handled by the ledger (and the engines) and applies to every parameter.
In the JSON config format, `ParamMaybe` is expressed by the `"optional": true` flag.
-}

type Param = (ParamKey, ParamValue)

{- Note [Manually constructing a Configuration value]

1. The `ConstitutionConfig` has to be sorted before it is passed to
the engine (requirement for the Sorted engine implementation).
2. The `ConstitutionConfig` should not contain duplicates.

Both 1 and 2 are guaranteed by construction only in case of using the JSON constitution format
and not when manually constructing a `ConstitutionConfig` ADT value.
-}

-- | See Note [Manually constructing a Configuration value]
newtype ConstitutionConfig = ConstitutionConfig {unConstitutionConfig :: [Param]}
  deriving stock (TH.Lift)
  deriving newtype (Haskell.Eq, Haskell.Show)

-- Taken from the older Reference impl: src/Cardano/Constitution/Validator/Reference/Types.hs
instance TH.Lift Tx.Rational where
  lift r =
    [|
      Tx.unsafeRatio
        $(TH.lift (Tx.numerator r))
        $(TH.lift (Tx.denominator r))
      |]
  liftTyped r =
    [||
    Tx.unsafeRatio
      $$(TH.liftTyped (Tx.numerator r))
      $$(TH.liftTyped (Tx.denominator r))
    ||]
