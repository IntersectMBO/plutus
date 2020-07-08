{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Marlowe.ACTUS.Ops where

import Language.Marlowe.ACTUS.Model.Utility.ContractRoleSign
    ( contractRoleSign )
import Language.Marlowe.ACTUS.Model.Utility.YearFraction ( yearFraction )
import Language.Marlowe.ACTUS.Definitions.ContractTerms ( ContractRole, DCC )
import Language.Marlowe
    ( Observation(ValueLT, ValueGT),
      Value(Cond, Constant, MulValue, Scale, AddValue, NegValue), (%) )
import Data.Time ( UTCTime(UTCTime), Day )
import Data.Time.Clock.System
    ( utcToSystemTime, SystemTime(MkSystemTime) )

class ActusOps a where
    _min :: a -> a -> a
    _max :: a -> a -> a
    _zero :: a
    _one :: a

class YearFractionOps a b where
    _y :: DCC -> a -> a -> a -> b

class DateOps a b where
    _lt :: a -> a -> b --returns pseudo-boolean

class RoleSignOps a where
    _r :: ContractRole -> a

instance ActusOps Double where
    _min  = min
    _max  = max
    _zero = 0.0
    _one  = 1.0

instance DateOps Day Double where
    _lt a b = if a < b then 1.0 else 0.0

instance YearFractionOps Day Double where
    _y = yearFraction

instance RoleSignOps Double where
    _r = contractRoleSign

instance ActusOps (Value Observation) where
    _min a b = Cond (ValueLT a b) a b
    _max a b = Cond (ValueGT a b) a b
    _zero = Constant 0
    _one  = Constant $ round marloweFixedPoint

instance DateOps (Value Observation) (Value Observation) where
    _lt a b = Cond (ValueLT a b) _one _zero

instance YearFractionOps (Value Observation) (Value Observation) where
    _y _ from to _ = (from - to) / Constant (360 * 24 * 60 * 60)

instance RoleSignOps (Value Observation) where
    _r x = Constant $ round $ contractRoleSign x

-------These orphans are never exposed to library users:
marloweFixedPoint = 1000

instance Num (Value Observation) where
    negate      = NegValue
    (+)         = AddValue
    a * b       = Scale (1 % 1000) $ MulValue a b
    fromInteger = Constant
    abs         = undefined
    signum      = undefined

instance Fractional (Value Observation) where
    recip (Constant x)          = Constant $ div 1 x
    recip _                     = undefined
    (Constant x) / (Constant y) = Constant $ div x y
    _ / _                       = undefined
    fromRational                = undefined