module Payoff where

open import Generated.Payoff
open import Definitions
open import Data.Integer

POF : ContractTerms → EventType → RiskFactors → ℤ
POF ct ev rf = + 0