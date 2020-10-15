{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}

module Language.Marlowe.ACTUS.MarloweOps where

import          Language.Marlowe                                      (Observation (ValueGT, ValueLT), Value (AddValue, Cond, Constant, MulValue, Scale, SubValue),
                                                                        (%))
import          Language.Marlowe.ACTUS.Ops
import          Language.Marlowe.ACTUS.Model.Utility.ContractRoleSign (contractRoleSign)

--this module is never exposed so orphans instances don't pose that much of a danger

instance ActusOps (Value Observation) where
    _min a b = Cond (ValueLT a b) a b
    _max a b = Cond (ValueGT a b) a b
    _zero = Constant 0
    _one  = Constant marloweFixedPoint

instance DateOps (Value Observation) (Value Observation) where
    _lt a b = Cond (ValueLT a b) _one _zero

instance RoleSignOps (Value Observation) where
    _r x = Constant $ (round $ contractRoleSign x) Prelude.* marloweFixedPoint

instance ActusNum (Value Observation) where
    (+)                         = AddValue
    (-)                         = SubValue
    a * b                       = Scale (1 % marloweFixedPoint) $ MulValue a b
    (Constant 0) / (Constant 0) = (Constant 0) -- by convention in finance
    (Constant x) / (Constant y) = Scale (marloweFixedPoint % 1) $ Constant $ div x y
    x / (Constant y)            = Scale (marloweFixedPoint % y) $ x
    _ / _                       = undefined --division not supported in Marlowe yet
