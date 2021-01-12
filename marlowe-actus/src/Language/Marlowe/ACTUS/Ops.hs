{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Marlowe.ACTUS.Ops where

import           Data.Time                                             (Day)
import           Language.Marlowe                                      (Observation (ValueGT, ValueLT), Value (AddValue, Cond, Constant, MulValue, Scale, SubValue),
                                                                        (%))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms      (ContractRole, DCC)
import           Language.Marlowe.ACTUS.Model.Utility.ContractRoleSign (contractRoleSign)
import           Language.Marlowe.ACTUS.Model.Utility.YearFraction     (yearFraction)

marloweFixedPoint :: Integer
marloweFixedPoint = 1000

class ActusOps a where
    _min :: a -> a -> a
    _max :: a -> a -> a
    _zero :: a
    _one :: a

class ActusNum a where
    (+) :: a -> a -> a
    (-) :: a -> a -> a
    (*) :: a -> a -> a
    (/) :: a -> a -> a

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

instance ActusNum Double where
    a + b       = a Prelude.+ b
    a - b       = a Prelude.- b
    a * b       = a Prelude.* b
    a / b       = a Prelude./ b

instance DateOps Day Double where
    _lt a b = if a < b then _one else _zero

instance YearFractionOps Day Double where
    _y = yearFraction

instance RoleSignOps Double where
    _r = contractRoleSign

instance ActusOps (Value Observation) where
    _min a b = Cond (ValueLT a b) a b
    _max a b = Cond (ValueGT a b) a b
    _zero = Constant 0
    _one  = Constant marloweFixedPoint

instance DateOps (Value Observation) (Value Observation) where
    _lt a b = Cond (ValueLT a b) _one _zero

instance RoleSignOps (Value Observation) where
    _r x = Constant $ (round $ contractRoleSign x) Prelude.* marloweFixedPoint


infixl 7  *, /
infixl 6  +, -

instance ActusNum (Value Observation) where
    (+)                         = AddValue
    (-)                         = SubValue
    a * b                       = Scale (1 % marloweFixedPoint) $ MulValue a b
    (Constant 0) / (Constant 0) = (Constant 0) -- by convention in finance
    (Constant x) / (Constant y) = Scale (marloweFixedPoint % 1) $ Constant $ div x y
    x / (Constant y)            = Scale (marloweFixedPoint % y) $ x
    _ / _                       = undefined --division not supported in Marlowe yet
