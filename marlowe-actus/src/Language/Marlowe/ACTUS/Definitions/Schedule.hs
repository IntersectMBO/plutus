module Language.Marlowe.ACTUS.Definitions.Schedule where

import           Data.Time                                         (Day)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType)

data ShiftedDay = ShiftedDay {
    paymentDay     :: Day,
    calculationDay :: Day
} deriving (Eq, Ord)

type ShiftedSchedule = [ShiftedDay]

data CashFlow = CashFlow {
    tick               :: Integer,
    cashContractId     :: String,
    cashParty          :: String,
    cashCounterParty   :: String,
    cashPaymentDay     :: Day,
    cashCalculationDay :: Day,
    cashEvent          :: EventType,
    amount             :: Double,
    currency           :: String
} deriving (Show)

