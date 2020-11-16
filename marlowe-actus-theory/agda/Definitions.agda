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