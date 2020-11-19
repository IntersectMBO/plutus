module Payoff where

open import Generated.Payoff
open import Definitions
open import Data.Integer

POF : ContractState → ContractTerms → EventType → RiskFactors → ℤ → ℤ
POF st ct PY rf y_sd_t = 
    (resolvePYTP (ContractTerms.ct_PYTP ct)) (RiskFactors.o_rf_CURS rf) (RiskFactors.o_rf_RRMO rf) (ContractTerms.ct_PYRT ct) (ContractTerms.ct_cPYRT ct) (ContractTerms.ct_CNTRL ct) (ContractState.nt st) (ContractState.ipnr st) y_sd_t
    where 
    resolvePYTP : PYTP → (ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    resolvePYTP PYTP.PYTP_A = _POF_PY_PAM_PYTP_A 
    resolvePYTP PYTP.PYTP_N = _POF_PY_PAM_PYTP_N   
    resolvePYTP PYTP.PYTP_I = _POF_PY_PAM_PYTP_I   
    resolvePYTP PYTP.PYTP_O = _POF_PY_PAM_PYTP_O 

POF st ct ev rf y_sd_t = + 0
