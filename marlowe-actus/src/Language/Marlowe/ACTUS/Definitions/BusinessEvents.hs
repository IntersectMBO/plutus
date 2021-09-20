{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Language.Marlowe.ACTUS.Definitions.BusinessEvents where

import           Data.Aeson.Types (ToJSON)
import           GHC.Generics     (Generic)
import           Language.Marlowe (Observation, Value)

{-| ACTUS event types
    https://github.com/actusfrf/actus-dictionary/blob/master/actus-dictionary-event.json
-}
data EventType =
      IED  -- ^ Initial Exchange
    | FP   -- ^ Fee Payment
    | PR   -- ^ Principal Redemption
    | PD   -- ^ Principal Drawing
    | PY   -- ^ Penalty Payment
    | PP   -- ^ Principal Prepayment (unscheduled event)
    | IP   -- ^ Interest Payment
    | IPCI -- ^ Interest Capitalization
    | CE   -- ^ Credit Event
    | RRF  -- ^ Rate Reset Fixing with Known Rate
    | RR   -- ^ Rate Reset Fixing with Unknown Rate
    | PRF  -- ^ Principal Payment Amount Fixing
    | DV   -- ^ Dividend Payment
    | PRD  -- ^ Purchase
    | MR   -- ^ Margin Call
    | TD   -- ^ Termination
    | SC   -- ^ Scaling Index Fixing
    | IPCB -- ^ Interest Calculation Base Fixing
    | MD   -- ^ Maturity
    | XD   -- ^ Exercise
    | STD  -- ^ Settlement
    | PI   -- ^ Principal Increase
    | AD   -- ^ Monitoring
    deriving (Eq, Show, Read, Ord, Enum)

{-| Risk factor observer
-}
data RiskFactorsPoly a = RiskFactorsPoly
    { o_rf_CURS :: a
    , o_rf_RRMO :: a
    , o_rf_SCMO :: a
    , pp_payoff :: a
    }
    deriving stock (Generic)
    deriving (Show, ToJSON)

type RiskFactors = RiskFactorsPoly Double
type RiskFactorsMarlowe = RiskFactorsPoly (Value Observation)
