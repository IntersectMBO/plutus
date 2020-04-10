module Language.Marlowe.ACTUS.HP.BusinessEvents where
import Data.Time

data EventType = AD | IED | PR | PI | PRF | PY | FP | PRD | TD | IP | IPCI | IPCB | RR

data ScheduledEvent = AD_EVENT {curs :: Double}  -- Analysis Event Retrieves current contract states without alter these
                    | IED_EVENT {curs :: Double}   -- Initial Exchange Date Scheduled date of first principal event, start of accrual calculation
                    | PR_EVENT {curs :: Double}   -- Principal Redemption Scheduled principal redemption payment
                    | PI_EVENT {curs :: Double}   -- Principal Increase Scheduled principal increase payments
                    | PRF_EVENT {curs :: Double}  -- Principal Payment Amount Fixing Scheduled re-fixing of principal payment (PR or PI) amount
                    | PY_EVENT {curs :: Double}   -- Penalty Payment Payment of a penalty (e.g. due to early repayment of principal outstanding)
                    | FP_EVENT {curs :: Double}   -- Fee Payment Scheduled fee payment
                    | PRD_EVENT {curs :: Double}  -- Purchase Date Purchase date of a contract bought in the secondary market
                    | TD_EVENT {curs :: Double}   -- Termination Date Sell date of a contract sold in the secondary market
                    | IP_EVENT {curs :: Double}   -- Interest Payment Scheduled interest payment
                    | IPCI_EVENT {curs :: Double}  -- Interest Capitalization Scheduled interest payment which is capitalized instead of paid out
                    | IPCB_EVENT {curs :: Double} -- Interest Payment Calculation Base Scheduled update to the calculation base for IP accruing
                    | RR_EVENT {curs :: Double}   -- Rate Reset Variable Scheduled rate reset event where new rate is fixed at event time
                    | RRF_EVENT {curs :: Double}   -- Rate Reset Fixed Scheduled rate reset event where new rate is already fixed
                    | SC_EVENT {curs :: Double}   -- Scaling Index Revision Scheduled re-fixing of a scaling index
                    | XD_EVENT {curs :: Double}   -- Execution Date Scheduled or unscheduled execution of e.g. an OPTNS or FUTUR contract
                    | DV_EVENT {curs :: Double}   -- Dividend Payment Scheduled (e.g. announced) dividend payment
                    | MR_EVENT {curs :: Double}   -- Margin Call Date Scheduled margin call event
                    | STD_EVENT {curs :: Double}  -- Settlement Date Date when payment for derivatives is settled
                    | MD_EVENT {curs :: Double}   -- Maturity Date Scheduled maturity or expiry of a contract
                    -- UNSCHEDULED
                    | PP_EVENT { payoff :: Double, curs :: Double} 
                    | CE_EVENT { date :: Day, curs :: Double} -- Credit event of counterparty to a contract
                    deriving (Eq, Ord, Show)
                     

