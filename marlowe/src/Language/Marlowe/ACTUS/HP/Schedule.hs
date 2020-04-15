module Language.Marlowe.ACTUS.HP.Schedule where
import Data.Time
import Language.Marlowe.ACTUS.HP.BusinessEvents

type Schedule = [Day]

data ShiftedDay = ShiftedDay {
    paymentDay :: Day,
    calculationDay :: Day
}

type ShiftedSchedule = [ShiftedDay]

data EventDay = EventDay {
    eventDay :: ShiftedDay,
    event :: ScheduledEvent,
    contractId :: String --todo we'll need separate contractId type with order that makes sub-contracts smaller than their parents
}

type EventSchedule = [EventDay]

data CashFlow = CashFlow {
    shiftedDay :: ShiftedDay,
    cashEvent :: ScheduledEvent,
    amount :: Double,
    currency :: String
}

type CashFlows = [CashFlow]