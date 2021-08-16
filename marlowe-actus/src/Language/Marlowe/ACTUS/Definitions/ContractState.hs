module Language.Marlowe.ACTUS.Definitions.ContractState where

import           Data.Time                                        (Day)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (PRF)

type ContractState = ContractStatePoly Double Day

{-| ACTUS Contract states are defined in
    https://github.com/actusfrf/actus-dictionary/blob/master/actus-dictionary-states.json
-}
data ContractStatePoly a b = ContractStatePoly
  {
    tmd   :: b    -- Maturity Date (MD): The timestamp as per which the contract matures according to the initial terms or as per unscheduled events
  , nt    :: a    -- Notional Principal (NT): The outstanding nominal value
  , ipnr  :: a    -- Nominal Interest Rate (IPNR) : The applicable nominal rate
  , ipac  :: a    -- Accrued Interest (IPAC): The current value of accrued interest
  , feac  :: a    -- Fee Accrued (FEAC): The current value of accrued fees
  , fac   :: a    -- TODO: feac vs. fac?
  , nsc   :: a    -- Notional Scaling Multiplier (SCNT): The multiplier being applied to principal cash flows
  , isc   :: a    -- InterestScalingMultiplier (SCIP): The multiplier being applied to interest cash flows
  , prf   :: PRF  -- Contract Performance (PRF)
  , sd    :: b    -- Status Date (MD): The timestamp as per which the state is captured at any point in time
  , prnxt :: a    -- Next Principal Redemption Payment (PRNXT): The value at which principal is being repaid
  , ipcb  :: a    -- Interest Calculation Base (IPCB)
  } deriving (Show)

