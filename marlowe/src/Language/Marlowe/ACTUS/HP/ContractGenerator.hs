module Language.Marlowe.ACTUS.HP.ContractGenerator where

import Language.Marlowe.ACTUS.HP.Control
import Language.Marlowe
import Data.Time

genContractFromPayOffSchedule :: [(Day, Amount, Currency)] -> Contract
genContractFromPayOffSchedule schedule = Close --foldl schedule $ (payment, )