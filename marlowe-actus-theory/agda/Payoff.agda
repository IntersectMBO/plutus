module Payoff where

open import Generated.Payoff
open import Definitions
open import Data.Integer

payoff : ContractTerms → EventType → RiskFactors → ℤ
payoff ct ev rf = + 0