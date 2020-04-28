module Language.Marlowe.ACTUS.HP.Schedule where
import Data.Time
import Language.Marlowe.ACTUS.HP.BusinessEvents

type Schedule = [Day]

data ShiftedDay = ShiftedDay {
    paymentDay :: Day,
    calculationDay :: Day
}

type ShiftedSchedule = [ShiftedDay]

data CashFlow = CashFlow {
    cashContractId :: String,
    cashParty :: String,
    cashCounterParty :: String,
    cashPaymentDay :: Day,
    cashEvent :: ScheduledEvent,
    amount :: Double,
    currency :: String
}

type CashFlows = [CashFlow]