module STF where
  open import Data.Integer
  open import Definitions
  open import Utils
  _STF_IED_PAM_ALL_tmd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_tmd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.tmd st)
  _STF_IED_PAM_ALL_nt : ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_nt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = ( (roleSign _CNTRL) * _NT)
  _STF_IED_PAM_ALL_ipnr :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_ipnr st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = _IPNR
  _STF_IED_PAM_ALL_ipac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_ipac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = _IPAC
  _STF_IED_PAM_ALL_feac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_feac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.feac st)
  _STF_IED_PAM_ALL_fac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_fac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.fac st)
  _STF_IED_PAM_ALL_nsc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_nsc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.nsc st)
  _STF_IED_PAM_ALL_isc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_isc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_ALL_sd : ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_sd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_ALL_prnxt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_prnxt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_ALL_ipcb :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_ALL_ipcb st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_IPANX_tmd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_tmd st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.tmd st)
  _STF_IED_PAM_IPNR_IPANX_nt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_nt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = ( (roleSign _CNTRL) * _NT)
  _STF_IED_PAM_IPNR_IPANX_ipnr :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_ipnr st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = _IPNR
  _STF_IED_PAM_IPNR_IPANX_ipac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_ipac st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (
       ( ( (pseudoLt _IPANX t) * y_ipanx_t) * ( (roleSign _CNTRL) * _NT))
       * _IPNR)
  _STF_IED_PAM_IPNR_IPANX_feac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_feac st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.feac st)
  _STF_IED_PAM_IPNR_IPANX_fac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_fac st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.fac st)
  _STF_IED_PAM_IPNR_IPANX_nsc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_nsc st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.nsc st)
  _STF_IED_PAM_IPNR_IPANX_isc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_isc st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_IPANX_sd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_sd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_IPANX_prnxt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_prnxt st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_IPANX_ipcb :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPANX_ipcb st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_IPAC_tmd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_tmd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.tmd st)
  _STF_IED_PAM_IPNR_IPAC_nt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_nt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = ( (roleSign _CNTRL) * _NT)
  _STF_IED_PAM_IPNR_IPAC_ipnr :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_ipnr st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = _IPNR
  _STF_IED_PAM_IPNR_IPAC_ipac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_ipac st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = _IPAC
  _STF_IED_PAM_IPNR_IPAC_feac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_feac st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.feac st)
  _STF_IED_PAM_IPNR_IPAC_fac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_fac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.fac st)
  _STF_IED_PAM_IPNR_IPAC_nsc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_nsc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.nsc st)
  _STF_IED_PAM_IPNR_IPAC_isc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_isc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_IPAC_sd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_sd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_IPAC_prnxt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_prnxt st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_IPAC_ipcb :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_IPAC_ipcb st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPAC_IPANX_tmd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_tmd st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.tmd st)
  _STF_IED_PAM_IPAC_IPANX_nt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_nt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = ( (roleSign _CNTRL) * _NT)
  _STF_IED_PAM_IPAC_IPANX_ipnr :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_ipnr st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (+ 0)
  _STF_IED_PAM_IPAC_IPANX_ipac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_ipac st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = _IPAC
  _STF_IED_PAM_IPAC_IPANX_feac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_feac st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.feac st)
  _STF_IED_PAM_IPAC_IPANX_fac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_fac st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.fac st)
  _STF_IED_PAM_IPAC_IPANX_nsc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_nsc st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.nsc st)
  _STF_IED_PAM_IPAC_IPANX_isc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_isc st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPAC_IPANX_sd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_sd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPAC_IPANX_prnxt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_prnxt st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPAC_IPANX_ipcb :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_IPANX_ipcb st t y_ipanx_t _IPNR _IPANX _CNTRL
  _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPAC_tmd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_tmd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.tmd st)
  _STF_IED_PAM_IPAC_nt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_nt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = ( (roleSign _CNTRL) * _NT)
  _STF_IED_PAM_IPAC_ipnr :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_ipnr st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (+ 0)
  _STF_IED_PAM_IPAC_ipac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_ipac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = _IPAC
  _STF_IED_PAM_IPAC_feac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_feac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.feac st)
  _STF_IED_PAM_IPAC_fac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_fac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.fac st)
  _STF_IED_PAM_IPAC_nsc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_nsc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.nsc st)
  _STF_IED_PAM_IPAC_isc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_isc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPAC_sd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_sd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPAC_prnxt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_prnxt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPAC_ipcb :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPAC_ipcb st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPANX_tmd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_tmd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.tmd st)
  _STF_IED_PAM_IPANX_nt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_nt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = ( (roleSign _CNTRL) * _NT)
  _STF_IED_PAM_IPANX_ipnr :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_ipnr st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (+ 0)
  _STF_IED_PAM_IPANX_ipac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_ipac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (
       ( ( (pseudoLt _IPANX t) * y_ipanx_t) * ( (roleSign _CNTRL) * _NT))
       * (+ 0))
  _STF_IED_PAM_IPANX_feac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_feac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.feac st)
  _STF_IED_PAM_IPANX_fac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_fac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.fac st)
  _STF_IED_PAM_IPANX_nsc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_nsc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.nsc st)
  _STF_IED_PAM_IPANX_isc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_isc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPANX_sd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_sd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPANX_prnxt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_prnxt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPANX_ipcb :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPANX_ipcb st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_tmd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_tmd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.tmd st)
  _STF_IED_PAM_IPNR_nt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_nt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = ( (roleSign _CNTRL) * _NT)
  _STF_IED_PAM_IPNR_ipnr :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_ipnr st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = _IPNR
  _STF_IED_PAM_IPNR_ipac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_ipac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (+ 0)
  _STF_IED_PAM_IPNR_feac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_feac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.feac st)
  _STF_IED_PAM_IPNR_fac :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_fac st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.fac st)
  _STF_IED_PAM_IPNR_nsc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_nsc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.nsc st)
  _STF_IED_PAM_IPNR_isc :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_isc st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_sd :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_sd st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_prnxt :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_prnxt st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC
  _NT
    = (ContractState.isc st)
  _STF_IED_PAM_IPNR_ipcb :
    ContractState → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ
  _STF_IED_PAM_IPNR_ipcb st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT
    = (ContractState.isc st)