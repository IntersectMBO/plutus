{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}

module Language.Marlowe.ACTUS.Definitions.BusinessEvents where

import           Data.Aeson.Types (ToJSON)
import           GHC.Generics     (Generic)

data EventType =
    AD | IED | PR | PI | PRF | PY | FP | PRD | TD | IP | IPCI | IPCB | RR | PP | CE | MD | RRF | SC | STD | DV | XD | MR
    deriving (Eq, Show, Read, Ord)

data RiskFactors = RiskFactors
    { o_rf_CURS :: Double
    , o_rf_RRMO :: Double
    , o_rf_SCMO :: Double
    , pp_payoff :: Double
    }
    deriving stock (Generic)
    deriving (Show, ToJSON)
