module StateTransition where

open import Generated.StateTransition
open import Definitions
open import Data.Integer
open import Data.Maybe

STF : ContractState → ContractTerms → EventType → RiskFactors → ℤ → ℤ → ContractState
STF st ct IED rf t y_ipanx_t = resolveNullability (ContractTerms.ct_IPNR ct) (ContractTerms.ct_IPAC ct) (ContractTerms.ct_IPANX ct)
    where
    resolveNullability : (Maybe ℤ) → (Maybe ℤ) → (Maybe ℤ) → ContractState
    resolveNullability (just ipnr) (just ipac) (just ipanx) = 
        record {
            tmd =   _STF_IED_PAM_ALL_tmd   st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            nt =    _STF_IED_PAM_ALL_nt    st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipnr =  _STF_IED_PAM_ALL_ipnr  st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipac =  _STF_IED_PAM_ALL_ipac  st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            feac =  _STF_IED_PAM_ALL_feac  st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            fac =   _STF_IED_PAM_ALL_fac   st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            nsc =   _STF_IED_PAM_ALL_nsc   st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            isc =   _STF_IED_PAM_ALL_isc   st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            sd =    _STF_IED_PAM_ALL_sd    st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            prnxt = _STF_IED_PAM_ALL_prnxt st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipcb =  _STF_IED_PAM_ALL_ipcb  st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct)
        }
    resolveNullability (just ipnr) (just ipac) nothing = 
        record {
            tmd =   _STF_IED_PAM_IPNR_IPAC_tmd   st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            nt =    _STF_IED_PAM_IPNR_IPAC_nt    st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipnr =  _STF_IED_PAM_IPNR_IPAC_ipnr  st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipac =  _STF_IED_PAM_IPNR_IPAC_ipac  st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            feac =  _STF_IED_PAM_IPNR_IPAC_feac  st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            fac =   _STF_IED_PAM_IPNR_IPAC_fac   st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            nsc =   _STF_IED_PAM_IPNR_IPAC_nsc   st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            isc =   _STF_IED_PAM_IPNR_IPAC_isc   st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            sd =    _STF_IED_PAM_IPNR_IPAC_sd    st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            prnxt = _STF_IED_PAM_IPNR_IPAC_prnxt st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipcb =  _STF_IED_PAM_IPNR_IPAC_ipcb  st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct)
        }
    resolveNullability (just ipnr) nothing (just ipanx) = 
        record {
            tmd =   _STF_IED_PAM_IPNR_IPANX_tmd   st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            nt =    _STF_IED_PAM_IPNR_IPANX_nt    st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipnr =  _STF_IED_PAM_IPNR_IPANX_ipnr  st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipac =  _STF_IED_PAM_IPNR_IPANX_ipac  st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            feac =  _STF_IED_PAM_IPNR_IPANX_feac  st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            fac =   _STF_IED_PAM_IPNR_IPANX_fac   st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            nsc =   _STF_IED_PAM_IPNR_IPANX_nsc   st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            isc =   _STF_IED_PAM_IPNR_IPANX_isc   st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            sd =    _STF_IED_PAM_IPNR_IPANX_sd    st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            prnxt = _STF_IED_PAM_IPNR_IPANX_prnxt st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipcb =  _STF_IED_PAM_IPNR_IPANX_ipcb  st t y_ipanx_t ipnr ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct)
        }
    resolveNullability nothing (just ipac) (just ipanx) = 
        record {
            tmd =   _STF_IED_PAM_IPAC_IPANX_tmd   st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            nt =    _STF_IED_PAM_IPAC_IPANX_nt    st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipnr =  _STF_IED_PAM_IPAC_IPANX_ipnr  st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipac =  _STF_IED_PAM_IPAC_IPANX_ipac  st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            feac =  _STF_IED_PAM_IPAC_IPANX_feac  st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            fac =   _STF_IED_PAM_IPAC_IPANX_fac   st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            nsc =   _STF_IED_PAM_IPAC_IPANX_nsc   st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            isc =   _STF_IED_PAM_IPAC_IPANX_isc   st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            sd =    _STF_IED_PAM_IPAC_IPANX_sd    st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            prnxt = _STF_IED_PAM_IPAC_IPANX_prnxt st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipcb =  _STF_IED_PAM_IPAC_IPANX_ipcb  st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct)
        }
    resolveNullability nothing (just ipac) nothing = 
        record {
            tmd =   _STF_IED_PAM_IPAC_tmd   st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            nt =    _STF_IED_PAM_IPAC_nt    st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipnr =  _STF_IED_PAM_IPAC_ipnr  st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipac =  _STF_IED_PAM_IPAC_ipac  st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            feac =  _STF_IED_PAM_IPAC_feac  st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            fac =   _STF_IED_PAM_IPAC_fac   st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            nsc =   _STF_IED_PAM_IPAC_nsc   st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            isc =   _STF_IED_PAM_IPAC_isc   st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            sd =    _STF_IED_PAM_IPAC_sd    st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            prnxt = _STF_IED_PAM_IPAC_prnxt st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct);
            ipcb =  _STF_IED_PAM_IPAC_ipcb  st t y_ipanx_t (+ 0) (+ 0) (ContractTerms.ct_CNTRL ct) ipac (ContractTerms.ct_NT ct)
        }
    resolveNullability nothing nothing (just ipanx) = 
        record {
            tmd =   _STF_IED_PAM_IPANX_tmd   st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            nt =    _STF_IED_PAM_IPANX_nt    st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipnr =  _STF_IED_PAM_IPANX_ipnr  st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipac =  _STF_IED_PAM_IPANX_ipac  st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            feac =  _STF_IED_PAM_IPANX_feac  st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            fac =   _STF_IED_PAM_IPANX_fac   st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            nsc =   _STF_IED_PAM_IPANX_nsc   st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            isc =   _STF_IED_PAM_IPANX_isc   st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            sd =    _STF_IED_PAM_IPANX_sd    st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            prnxt = _STF_IED_PAM_IPANX_prnxt st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipcb =  _STF_IED_PAM_IPANX_ipcb  st t y_ipanx_t (+ 0) ipanx (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct)
        }
    resolveNullability (just ipnr) nothing nothing = 
        record {
            tmd =   _STF_IED_PAM_IPNR_tmd   st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            nt =    _STF_IED_PAM_IPNR_nt    st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipnr =  _STF_IED_PAM_IPNR_ipnr  st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipac =  _STF_IED_PAM_IPNR_ipac  st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            feac =  _STF_IED_PAM_IPNR_feac  st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            fac =   _STF_IED_PAM_IPNR_fac   st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            nsc =   _STF_IED_PAM_IPNR_nsc   st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            isc =   _STF_IED_PAM_IPNR_isc   st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            sd =    _STF_IED_PAM_IPNR_sd    st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            prnxt = _STF_IED_PAM_IPNR_prnxt st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct);
            ipcb =  _STF_IED_PAM_IPNR_ipcb  st t y_ipanx_t ipnr (+ 0) (ContractTerms.ct_CNTRL ct) (+ 0) (ContractTerms.ct_NT ct)
        }
    resolveNullability nothing nothing nothing = st
    
STF st ct ev rf t y_ipanx_t = st