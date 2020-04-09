{- Describes event types 
   Events could be scheduled or unscheduled.
   Unscheduled events are often parametrized
-}

module Language.Marlowe.ACTUS.HP.BusinessEvents where
import Data.Time

data BuisenessEvent = AD   -- Analysis Event Retrieves current contract states without alter these
                    | IED  -- Initial Exchange Date Scheduled date of first principal event, start of accrual calculation
                    | PR   -- Principal Redemption Scheduled principal redemption payment
                    | PI   -- Principal Increase Scheduled principal increase payments
                    | PRF  -- Principal Payment Amount Fixing Scheduled re-fixing of principal payment (PR or PI) amount
                    | PY   -- Penalty Payment Payment of a penalty (e.g. due to early repayment of principal outstanding)
                    | FP   -- Fee Payment Scheduled fee payment
                    | PRD  -- Purchase Date Purchase date of a contract bought in the secondary market
                    | TD   -- Termination Date Sell date of a contract sold in the secondary market
                    | IP   -- Interest Payment Scheduled interest payment
                    | IPCI -- Interest Capitalization Scheduled interest payment which is capitalized instead of paid out
                    | IPCB -- Interest Payment Calculation Base Scheduled update to the calculation base for IP accruing
                    | RR   -- Rate Reset Variable Scheduled rate reset event where new rate is fixed at event time
                    | RRF  -- Rate Reset Fixed Scheduled rate reset event where new rate is already fixed
                    | SC   -- Scaling Index Revision Scheduled re-fixing of a scaling index
                    | XD   -- Execution Date Scheduled or unscheduled execution of e.g. an OPTNS or FUTUR contract
                    | DV   -- Dividend Payment Scheduled (e.g. announced) dividend payment
                    | MR   -- Margin Call Date Scheduled margin call event
                    | STD  -- Settlement Date Date when payment for derivatives is settled
                    | MD   -- Maturity Date Scheduled maturity or expiry of a contract
                    -- UNSCHEDULED
                    | PP { payment :: Double } 
                    | CE { date :: Day} -- Credit event of counterparty to a contract
                    -- RISK FACTOR RESET
                    | CURS_UPDATE { exchangeRate :: Double } 
                    | SCMO_UPDATE { scalingIndex :: Double}
                    | RRMO_UPDATE { rate :: Double }
                    deriving (Eq, Ord, Show)
                     

