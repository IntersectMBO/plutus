module Language.Marlowe.ACTUS.HP.ContractGenerator where

import Language.Marlowe.ACTUS.HP.Control
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.Schedule
import Language.Marlowe.ACTUS.HP.BusinessEvents

import Language.Marlowe
import Data.Time
import Data.Map

genContract :: CashFlows -> Contract
genContract cashFlows = Close

genShiftedSchedule :: EventType -> ContractTerms -> ShiftedSchedule
genShiftedSchedule eventType terms = []

{- event sourcing: this would hold historical events needed to resume the contract -}
type ExternalState = EventSchedule

approximateEventSchedule :: Map EventType ShiftedSchedule -> ExternalState -> EventSchedule
approximateEventSchedule staticSchedule state = [] -- we need to merge ShiftedSchedule with events that happened already and propagate their risk factors

genCashFlows :: ContractTerms -> CashFlows
genCashFlows terms = []