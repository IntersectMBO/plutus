{- Describes event types 
   Events could be scheduled or unscheduled.
   Unscheduled events are often parametrized
-}

module Language.Marlowe.ACTUS.HP.BusinessEvents where
import Data.Time

data BuisenessEvent = AD {curs :: Double}  -- Analysis Event Retrieves current contract states without alter these
                    | IED {curs :: Double}   -- Initial Exchange Date Scheduled date of first principal event, start of accrual calculation
                    | PR {curs :: Double}   -- Principal Redemption Scheduled principal redemption payment
                    | PI {curs :: Double}   -- Principal Increase Scheduled principal increase payments
                    | PRF {curs :: Double}  -- Principal Payment Amount Fixing Scheduled re-fixing of principal payment (PR or PI) amount
                    | PY {curs :: Double}   -- Penalty Payment Payment of a penalty (e.g. due to early repayment of principal outstanding)
                    | FP {curs :: Double}   -- Fee Payment Scheduled fee payment
                    | PRD {curs :: Double}  -- Purchase Date Purchase date of a contract bought in the secondary market
                    | TD {curs :: Double}   -- Termination Date Sell date of a contract sold in the secondary market
                    | IP {curs :: Double}   -- Interest Payment Scheduled interest payment
                    | IPCI {curs :: Double}  -- Interest Capitalization Scheduled interest payment which is capitalized instead of paid out
                    | IPCB {curs :: Double} -- Interest Payment Calculation Base Scheduled update to the calculation base for IP accruing
                    | RR {curs :: Double}   -- Rate Reset Variable Scheduled rate reset event where new rate is fixed at event time
                    | RRF {curs :: Double}   -- Rate Reset Fixed Scheduled rate reset event where new rate is already fixed
                    | SC {curs :: Double}   -- Scaling Index Revision Scheduled re-fixing of a scaling index
                    | XD {curs :: Double}   -- Execution Date Scheduled or unscheduled execution of e.g. an OPTNS or FUTUR contract
                    | DV {curs :: Double}   -- Dividend Payment Scheduled (e.g. announced) dividend payment
                    | MR {curs :: Double}   -- Margin Call Date Scheduled margin call event
                    | STD {curs :: Double}  -- Settlement Date Date when payment for derivatives is settled
                    | MD {curs :: Double}   -- Maturity Date Scheduled maturity or expiry of a contract
                    -- UNSCHEDULED
                    | PP { payoff :: Double, curs :: Double} 
                    | CE { date :: Day, curs :: Double} -- Credit event of counterparty to a contract
                    deriving (Eq, Ord, Show)
                     

