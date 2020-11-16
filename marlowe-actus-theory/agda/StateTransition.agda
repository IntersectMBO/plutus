module StateTransition where

open import Generated.Payoff
open import Definitions
open import Data.Integer

stateTransition : ContractState → ContractTerms → EventType → RiskFactors → ContractState
stateTransition st ct ev rf = st