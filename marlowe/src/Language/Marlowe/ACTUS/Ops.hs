{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}

module Language.Marlowe.ACTUS.Ops where

import Language.Marlowe.ACTUS.Utility.ContractRoleSign
import Language.Marlowe.ACTUS.Utility.YearFraction
import Language.Marlowe.ACTUS.ContractTerms
import Language.Marlowe
import Data.Time
import Data.Time.Clock
import Data.Time.Clock.POSIX
import Data.Time.Clock.System

class ActusOps a where 
    _min :: a -> a -> a
    _max :: a -> a -> a
    _zero :: a
    _one :: a

class YearFractionOps a b where
    _y :: DCC -> a -> a -> a -> b

class RoleSignOps a where
    _r :: ContractRole -> a

instance ActusOps Double where
    _min = min
    _max = max
    _zero = 0.0
    _one = 1.0

instance YearFractionOps Day Double where
    _y = yearFraction

instance RoleSignOps Double where
    _r = contractRoleSign

instance ActusOps (Value Observation) where
    _min a b = (Cond (ValueLT a b) a b)
    _max a b = (Cond (ValueGT a b) a b)
    _zero = Constant 0
    _one = Constant $ round $ marloweFixedPoint

instance YearFractionOps (Value Observation) (Value Observation) where
    _y _ from to _ = (from - to) / (Constant (360 * 24 * 60 * 60))

instance RoleSignOps (Value Observation) where
    _r x = Constant $ round $ contractRoleSign x

cardanoEpochStart :: Integer
cardanoEpochStart = 100

dayToSlotNumber :: Day -> Integer
dayToSlotNumber d = let
    (MkSystemTime secs _) = utcToSystemTime (UTCTime d 0)
    in fromIntegral secs - cardanoEpochStart `mod` 20

slotRangeToDay :: Integer -> Integer -> Day
slotRangeToDay start end = undefined