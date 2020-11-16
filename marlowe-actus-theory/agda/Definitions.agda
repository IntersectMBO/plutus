module Definitions where

open import Data.Integer

record ContractState : Set where
  field
    tmd   : ℤ
    nt    : ℤ
    ipnr  : ℤ
    ipac  : ℤ
    feac  : ℤ
    fac   : ℤ
    nsc   : ℤ
    isc   : ℤ
    sd    : ℤ
    prnxt : ℤ
    ipcb  : ℤ

data FEB : Set where
    FEB_A : FEB
    FEB_N : FEB

data PYTP : Set where
    PYTP_A : PYTP
    PYTP_N : PYTP 
    PYTP_I : PYTP 
    PYTP_O : PYTP

data SCEF : Set where  
    SE000 : SCEF
    SE0N0 : SCEF
    SE00M : SCEF
    SE0NM : SCEF
    SEI00 : SCEF
    SEIN0 : SCEF
    SEI0M : SCEF
    SEINM : SCEF 

data ContractRole : Set where 
    CR_RPA : ContractRole -- Real position asset
    CR_RPL : ContractRole -- Real position liability
    CR_CLO : ContractRole -- Role of a collateral
    CR_CNO : ContractRole -- Role of a close-out-netting
    CR_COL : ContractRole -- Role of an underlying to a collateral
    CR_LG : ContractRole  -- Long position
    CR_ST : ContractRole  -- Short position
    CR_BUY : ContractRole -- Protection buyer
    CR_SEL : ContractRole -- Protection seller
    CR_RFL : ContractRole -- Receive first leg
    CR_PFL : ContractRole -- Pay first leg
    CR_RF : ContractRole  -- Receive fix leg
    CR_PF : ContractRole  -- Pay fix leg

data ContractType : Set where
    PAM : ContractType
    LAM : ContractType


record ContractTerms : Set where
  field
    contractType : ContractType
    ct_CNTRL     : ContractRole
    ct_PDIED     : ℤ -- Premium / Discount At IED
    ct_NT        : ℤ -- Notional
    ct_PPRD      : ℤ -- Price At Purchase Date
    ct_PTD       : ℤ -- Price At Termination Date
  -- Penalties
    ct_PYRT      : ℤ -- Penalty Rate
    ct_PYTP      : PYTP -- Penalty Pype
    ct_cPYRT     : ℤ
  -- Scaling:
    ct_SCIED     : ℤ
    ct_SCEF      : SCEF
    ct_SCIXSD    : ℤ
  -- Rate Reset
    ct_RRSP      : ℤ
    ct_RRMLT     : ℤ
    ct_RRPF      : ℤ
    ct_RRPC      : ℤ
    ct_RRLC      : ℤ
    ct_RRLF      : ℤ
  -- Interest
    ct_IPNR      : ℤ
    ct_IPAC      : ℤ
  -- Fee
    ct_FEAC      : ℤ
    ct_FEB       : FEB
    ct_FER       : ℤ