module Language.Marlowe.ACTUS.Definitions.BusinessEvents where
import           Data.Time (Day)


data EventType =
    AD | IED | PR | PI | PRF | PY | FP | PRD | TD | IP | IPCI | IPCB | RR | PP | CE | MD | RRF | SC | STD | DV | XD | MR
    deriving (Eq, Show)

data RiskFactors = RiskFactors
    { o_rf_CURS  :: Double
    , o_rf_RRMO  :: Double
    , o_rf_SCMO  :: Double
    , pp_payoff  :: Double
    , creditDate :: Day
    } deriving (Show)
