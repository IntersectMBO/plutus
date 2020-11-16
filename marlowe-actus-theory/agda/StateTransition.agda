module StateTransition where

open import Generated.Payoff
open import Definitions
open import Data.Integer

STF : ContractState → ContractTerms → EventType → RiskFactors → ContractState
STF st ct ev rf = st