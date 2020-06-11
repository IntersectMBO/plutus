{-# LANGUAGE ExistentialQuantification #-}
module Language.Marlowe.ACTUS.ContractState where

import Data.Time ( Day )
import Data.Map ( Map )


-- all contract states in a composite contract
type ContractStateContext = Map String ContractState

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
                    deriving (Show, Eq)
