{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE ExistentialQuantification #-}
module Language.Marlowe.ACTUS.Definitions.ContractState where

import           Data.Time                                        (Day)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (PRF)

type ContractState = ContractStatePoly Double Day

data ContractStatePoly a b = ContractStatePoly
  {
  tmd     :: b
  , nt    :: a
  , ipnr  :: a
  , ipac  :: a
  , feac  :: a
  , fac   :: a
  , nsc   :: a
  , isc   :: a
  , prf   :: PRF
  , sd    :: b
  , prnxt :: a
  , ipcb  :: a
  } deriving (Show)

