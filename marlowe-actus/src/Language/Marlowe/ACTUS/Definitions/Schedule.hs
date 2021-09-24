module Language.Marlowe.ACTUS.Definitions.Schedule where

import           Data.Time                                         (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType)

data ShiftedDay = ShiftedDay {
    paymentDay     :: LocalTime,
    calculationDay :: LocalTime
} deriving (Eq, Ord, Show)

type ShiftedSchedule = [ShiftedDay]

data CashFlow = CashFlow {
    tick               :: Integer,
    cashContractId     :: String,
    cashParty          :: String,
    cashCounterParty   :: String,
    cashPaymentDay     :: LocalTime,
    cashCalculationDay :: LocalTime,
    cashEvent          :: EventType,
    amount             :: Double,
    currency           :: String
} deriving (Show)

