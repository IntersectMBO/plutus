{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
module Language.Marlowe.ACTUS.Definitions.ContractState where

import           Data.Time ( Day )
import           Data.Aeson.Types           hiding (Error, Value)
import           GHC.Generics (Generic)

type ContractState = ContractStatePoly Double Day

data ContractStatePoly a b = ContractStatePoly
  {
  tmd :: b
  , nt  :: a
  , ipnr :: a
  , ipac :: a
  , feac :: a
  , fac :: a
  , nsc :: a
  , isc :: a
  , prf :: ContractStatus
  , sd :: b
  , prnxt :: a
  , ipcb :: a
  } deriving (Show)

  -- CS – Indicates different states of the contract from performance to default
data ContractStatus = CS_PF -- performant
                    | CS_DL -- delayed
                    | CS_DQ -- delinquent
                    | CS_DF -- default
                    deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)
