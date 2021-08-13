{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Language.Marlowe.ACTUS.Definitions.BusinessEvents where

import           Data.Aeson.Types (ToJSON)
import           Data.Map
import           Data.Time
import           GHC.Generics     (Generic)

{-| ACTUS event types
    https://github.com/actusfrf/actus-dictionary/blob/master/actus-dictionary-event.json
-}
data EventType =
      AD   -- Monitoring
    | IED  -- Initial Exchange
    | PR   -- Principal Redemption
    | PI   -- ?
    | PRF  -- Principal Payment Amount Fixing
    | PY   -- Penalty Payment
    | FP   -- Fee Payment
    | PRD  -- Purchase
    | TD   -- Termination
    | IP   -- Interest Payment
    | IPCI -- Interest Capitalization
    | IPCB -- Interest Calculation Base Fixing
    | RR   -- Rate Reset Fixing with Unknown Rate
    | PP   -- Principal Prepayment (unscheduled event)
    | CE   -- Credit Event
    | MD   -- Maturity
    | RRF  -- Rate Reset Fixing with Known Rate
    | SC   -- Scaling Index Fixing
    | STD  -- Settlement
    | DV   -- Dividend Payment
    | XD   -- Exercise
    | MR   -- Margin Call
    deriving (Eq, Show, Read, Ord)

data RiskFactors = RiskFactors
    { o_rf_CURS :: Double
    , o_rf_RRMO :: Double
    , o_rf_SCMO :: Double
    , pp_payoff :: Double
    }
    deriving stock (Generic)
    deriving (Show, ToJSON)

type DataObserved = Map String ValuesObserved

data ValuesObserved = ValuesObserved
  { identifier :: String
  , values     :: [ValueObserved]
  }
  deriving (Show)

data ValueObserved = ValueObserved
  { timestamp :: Day
  , value     :: Double
  }
  deriving (Show)
