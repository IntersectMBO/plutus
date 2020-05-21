{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Marlowe.ACTUS.Ops where

import Language.Marlowe.ACTUS.Utility.ContractRoleSign
import Language.Marlowe.ACTUS.Utility.YearFraction
import Language.Marlowe.ACTUS.ContractTerms
import Data.Time

class ActusOps a where 
    _min :: a -> a -> a
    _max :: a -> a -> a
    _zero :: a

class YearFractionOps a b where
    _y :: DCC -> a -> a -> a -> b

class RoleSignOps a where
    _r :: ContractRole -> a

instance ActusOps Double where
    _min = min
    _max = max
    _zero = 0.0

instance YearFractionOps Day Double where
    _y = yearFraction

instance RoleSignOps Double where
    _r = contractRoleSign