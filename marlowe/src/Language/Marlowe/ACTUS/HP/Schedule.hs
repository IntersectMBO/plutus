module Language.Marlowe.ACTUS.HP.Schedule where
import Data.Time

type Schedule = [Day]

data ShiftedDay = ShiftedDay {
    paymentDay :: Day,
    calculationDay :: Day
}

type ShiftedSchedule = [ShiftedDay]

data CashFlow = CashFlow {
    day :: ShiftedDay,
    amount :: Double,
    currency :: String
}

type CashFlows = [CashFlow]