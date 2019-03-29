{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
module Marlowe where

import           GHC.Generics            (Generic)
import           Language.Marlowe.Pretty as Pretty

prettyPrint :: Contract -> String
prettyPrint = show . Pretty.pretty

type BlockNumber = Integer
type Timeout = BlockNumber
type Person = Integer
type Choice = Integer

type IdAction = Integer
type IdCommit = Integer
type IdChoice = (Integer, Person)
type IdOracle = Integer

type LetLabel = Integer

data Value = CurrentBlock |
             Committed IdCommit |
             Constant Integer |
             NegValue Value |
             AddValue Value Value |
             SubValue Value Value |
             MulValue Value Value |
             DivValue Value Value Value |
 --          dividend-^ divisor-^ ^-default value (in case divisor is zero)
             ModValue Value Value Value |
 --          dividend-^ divisor-^ ^-default value (in case divisor is zero)
             ValueFromChoice IdChoice Value |
 --    default value if not available --^
             ValueFromOracle IdOracle Value
 --    default value if not available --^
               deriving stock (Eq, Ord, Show, Generic, Read)
               deriving anyclass (Pretty.Pretty)

data Observation = BelowTimeout Timeout |
                   AndObs Observation Observation |
                   OrObs Observation Observation |
                   NotObs Observation |
                   ChoseThis IdChoice Choice |
                   ChoseSomething IdChoice |
                   ValueGE Value Value |
                   ValueGT Value Value |
                   ValueLT Value Value |
                   ValueLE Value Value |
                   ValueEQ Value Value |
                   TrueObs |
                   FalseObs
               deriving stock (Eq, Ord, Show, Generic, Read)
               deriving anyclass (Pretty.Pretty)

data Contract =
    Null |
    Commit !IdAction !IdCommit !Person !Value !Timeout !Timeout !Contract !Contract |
    Pay !IdAction !IdCommit !Person !Value !Timeout !Contract !Contract |
    Both !Contract !Contract |
    Choice !Observation !Contract !Contract |
    When !Observation !Timeout !Contract !Contract |
    While !Observation !Timeout !Contract !Contract |
    Scale !Value !Value !Value !Contract |
    Let !LetLabel !Contract !Contract |
    Use !LetLabel
               deriving stock (Eq, Ord, Show, Generic, Read)
               deriving anyclass (Pretty.Pretty)

