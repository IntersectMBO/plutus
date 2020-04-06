module Language.Marlowe.ACTUS.HP.Observations where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Maybe as Maybe
import Language.Marlowe.ACTUS.HP.BusinessEvents
import Language.Marlowe.ACTUS.HP.ContractTerms
import Language.Marlowe.ACTUS.HP.ContractState

data TimeStamp = Integer --todo how do we respond to outdated RiskEvents

{- Observation of a risk factor -}
orf :: RiskFactor -> TimeStamp -> ContractState -> GenericContractTerms -> Double
orf i t _S _M = let 
    (datadate, riskEvent) = fromJust $ Map.lookup i (risks _S) --todo throw a readable error
    in case riskEvent of
        CURS_UPDATE {} -> exchangeRate riskEvent
        SCMO_UPDATE {} -> scalingIndex riskEvent

{- Observation of unscheduled event -}
-- oev :: RiskFactor -> UnscheduledEvent
-- oev = id

{- payoff of unscheduled event -}
f_payoff :: UnscheduledEvent -> Double
f_payoff e = case e of
    PP {payment = p} -> p



