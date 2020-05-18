module Language.Marlowe.ACTUS.BusinessEvents where
import Data.Time

data EventType = 
    AD | IED | PR | PI | PRF | PY | FP | PRD | TD | IP | IPCI | IPCB | RR | PP | CE | MD | RRF | SC | STD | DV | XD | MR
    deriving (Enum)

data ScheduledEvent = AD_EVENT {o_rf_CURS :: Double}  -- Analysis Event Retrieves current contract states without alter these
                    | IED_EVENT {o_rf_CURS :: Double}   -- Initial Exchange Date Scheduled date of first principal event, start of accrual calculation
                    | PR_EVENT {o_rf_CURS :: Double}   -- Principal Redemption Scheduled principal redemption payment
                    | PI_EVENT {o_rf_CURS :: Double}   -- Principal Increase Scheduled principal increase payments
                    | PRF_EVENT {o_rf_CURS :: Double}  -- Principal Payment Amount Fixing Scheduled re-fixing of principal payment (PR or PI) amount
                    | PY_EVENT {o_rf_CURS :: Double, o_rf_RRMO :: Double}   -- Penalty Payment Payment of a penalty (e.g. due to early repayment of principal outstanding)
                    | FP_EVENT {o_rf_CURS :: Double}   -- Fee Payment Scheduled fee payment
                    | PRD_EVENT {o_rf_CURS :: Double}  -- Purchase Date Purchase date of a contract bought in the secondary market
                    | TD_EVENT {o_rf_CURS :: Double}   -- Termination Date Sell date of a contract sold in the secondary market
                    | IP_EVENT {o_rf_CURS :: Double}   -- Interest Payment Scheduled interest payment
                    | IPCI_EVENT {o_rf_CURS :: Double}  -- Interest Capitalization Scheduled interest payment which is capitalized instead of paid out
                    | IPCB_EVENT {o_rf_CURS :: Double} -- Interest Payment Calculation Base Scheduled update to the calculation base for IP accruing
                    | RR_EVENT {o_rf_CURS :: Double, o_rf_RRMO :: Double}   -- Rate Reset Variable Scheduled rate reset event where new rate is fixed at event time
                    | RRF_EVENT {o_rf_CURS :: Double}   -- Rate Reset Fixed Scheduled rate reset event where new rate is already fixed
                    | SC_EVENT {o_rf_CURS :: Double, o_rf_SCMO :: Double}   -- Scaling Index Revision Scheduled re-fixing of a scaling index
                    | XD_EVENT {o_rf_CURS :: Double}   -- Execution Date Scheduled or unscheduled execution of e.g. an OPTNS or FUTUR contract
                    | DV_EVENT {o_rf_CURS :: Double}   -- Dividend Payment Scheduled (e.g. announced) dividend payment
                    | MR_EVENT {o_rf_CURS :: Double}   -- Margin Call Date Scheduled margin call event
                    | STD_EVENT {o_rf_CURS :: Double}  -- Settlement Date Date when payment for derivatives is settled
                    | MD_EVENT {o_rf_CURS :: Double}   -- Maturity Date Scheduled maturity or expiry of a contract
                    -- UNSCHEDULED
                    | PP_EVENT { pp_payoff :: Double, o_rf_CURS :: Double} 
                    | CE_EVENT { date :: Day, o_rf_CURS :: Double} -- Credit event of counterparty to a contract
                    deriving (Eq, Ord, Show)
                     
mapEventType :: ScheduledEvent -> EventType
mapEventType event = case event of {
    _ -> PP --todo
}

eventTypeIdToEventType :: Integer -> EventType
eventTypeIdToEventType id = AD --todo
