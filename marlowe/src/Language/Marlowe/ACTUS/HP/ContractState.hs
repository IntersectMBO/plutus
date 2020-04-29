module Language.Marlowe.ACTUS.HP.ContractState where

import Data.Time
import Data.Map

-- all contract states in a composite contract
type ContractStateContext = Map String ContractState

data ContractState = ContractState
  { 
  tmd :: Day
  , nt  :: Double
  , ipnr :: Double
  , ipac :: Double
  , feac :: Double
  , fac :: Double
  , nsc :: Double
  , isc :: Double
  , prf :: ContractStatus
  , sd :: Day
  , prnxt :: Double
  , ipcb :: Double
  } deriving (Show)

  -- CS – Indicates different states of the contract from performance to default
data ContractStatus = CS_PF -- performant
                    | CS_DL -- delayed
                    | CS_DQ -- delinquent
                    | CS_DF -- default
                    deriving (Show, Eq)