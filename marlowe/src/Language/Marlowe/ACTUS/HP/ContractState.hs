module Language.Marlowe.ACTUS.HP.ContractState where

import Data.Time
import Data.Map (Map)
import qualified Data.Map as Map
import Language.Marlowe.ACTUS.HP.BusinessEvents
import Data.Maybe
import qualified Data.Maybe as Maybe

data ContractState = ContractState
  { 
    contractId :: String  
  , t0  :: Day
  , tmd :: Day
  , nt  :: Double
  , ipnr :: Double
  , ipac :: Double
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