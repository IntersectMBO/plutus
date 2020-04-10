module Language.Marlowe.ACTUS.HP.ContractGenerator where

import Language.Marlowe.ACTUS.HP.Control
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.Schedule

import Language.Marlowe
import Data.Time

genContractFromCashFlows :: CashFlows -> Contract
genContractFromCashFlows cashFlows = Close

genShiftedSchedule :: ContractTerms -> ShiftedSchedule
genShiftedSchedule terms = []

genCashFlows :: ContractTerms -> CashFlows
genCashFlows schedule = []