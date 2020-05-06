module Language.Marlowe.ACTUS.Schedule where
import Data.Time
import Language.Marlowe.ACTUS.BusinessEvents

type Schedule = [Day]

data ShiftedDay = ShiftedDay {
    paymentDay :: Day,
    calculationDay :: Day
} deriving (Eq, Ord)

type ShiftedSchedule = [ShiftedDay]

data CashFlow = CashFlow {
    tick :: Integer,
    cashContractId :: String,
    cashParty :: String,
    cashCounterParty :: String,
    cashPaymentDay :: Day,
    cashCalculationDay :: Day,
    cashEvent :: ScheduledEvent,
    amount :: Double,
    currency :: String
}

type CashFlows = [CashFlow]