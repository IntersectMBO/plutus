{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransitionModel where

import           Data.Maybe                                        (fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState  (ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  (ContractTermsPoly (..), FEB (..), IPCB (..),
                                                                    SCEF (..))
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Annuity  (annuity)
import           Language.Marlowe.ACTUS.Ops                        (ActusNum (..), ActusOps (..), DateOps (_lt),
                                                                    RoleSignOps (_r))
import           Prelude                                           hiding (Fractional, Num, (*), (+), (-), (/))

-- Principal at Maturity (PAM)

_STF_AD_PAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_AD_PAM st@ContractStatePoly {..} t y_sd_t =
  st
    { ipac = ipac + y_sd_t * ipnr * nt,
      sd = t
    }

_STF_IED_PAM :: (RoleSignOps a, DateOps b a) => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_IED_PAM
  ContractTermsPoly
    { ct_CNTRL = cntrl,
      ct_IPNR = nominalInterestRate,
      ct_NT = Just notionalPrincipal,
      ct_IPAC = Just accruedInterest
    }
  st
  t
  _ =
    st
      { nt = _r cntrl * notionalPrincipal,
        ipnr = fromMaybe _zero nominalInterestRate,
        ipac = accruedInterest,
        sd = t
      }
_STF_IED_PAM
  ContractTermsPoly
    { ct_CNTRL = cntrl,
      ct_IPNR = nominalInterestRate,
      ct_NT = Just notionalPrincipal,
      ct_IPANX = Just anchorInterestPayment
    }
  st
  t
  y_ipanx_t =
    let nt' = _r cntrl * notionalPrincipal
        ipnr' = fromMaybe _zero nominalInterestRate
     in st
          { nt = nt',
            ipnr = ipnr',
            ipac = _lt anchorInterestPayment t * y_ipanx_t * nt' * ipnr',
            sd = t
          }
_STF_IED_PAM _ st _ _ = st

_STF_MD_PAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_MD_PAM st t =
  st
    { nt = _zero,
      ipac = _zero,
      feac = _zero,
      sd = t
    }

_STF_PP_PAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> RiskFactorsPoly a -> b -> a -> a -> a -> ContractStatePoly a b
_STF_PP_PAM ct st@ContractStatePoly {..} RiskFactorsPoly {..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus =
  let st' = _STF_PY_PAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
   in st'
        { nt = nt - pp_payoff
        }

_STF_PY_PAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> ContractStatePoly a b
_STF_PY_PAM
  ContractTermsPoly
    { ct_FEB = Just FEB_N,
      ct_FER = Just feeRate,
      ct_NT = Just notionalPrincipal
    }
  st@ContractStatePoly {..}
  t
  y_sd_t
  _
  _ =
    st
      { ipac = ipac + y_sd_t * ipnr * nt,
        feac = feac + y_sd_t * notionalPrincipal * feeRate,
        sd = t
      }
_STF_PY_PAM
  ContractTermsPoly
    { ct_FER = Just feeRate,
      ct_CNTRL = cntrl
    }
  st@ContractStatePoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let
     in st
          { ipac = ipac + y_sd_t * ipnr * nt,
            feac = _max _zero (y_tfpminus_t / y_tfpminus_tfpplus) * _r cntrl * feeRate,
            sd = t
          }
_STF_PY_PAM _ st _ _ _ _ = st

_STF_FP_PAM :: (ActusNum a, ActusOps a) => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_FP_PAM st@ContractStatePoly {..} t y_sd_t =
  st
    { ipac = ipac + y_sd_t * ipnr * nt,
      feac = _zero,
      sd = t
    }

_STF_PRD_PAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> ContractStatePoly a b
_STF_PRD_PAM = _STF_PY_PAM

_STF_TD_PAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_TD_PAM st t =
  st
    { nt = _zero,
      ipac = _zero,
      feac = _zero,
      ipnr = _zero,
      sd = t
    }

_STF_IP_PAM :: (ActusOps a, ActusNum a) => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_IP_PAM
  ContractTermsPoly
    { ct_FER = Just fer
    }
  st@ContractStatePoly {..}
  t
  y_sd_t =
    st
      { ipac = _zero,
        feac = y_sd_t * fer * nt,
        sd = t
      }
_STF_IP_PAM
  _
  st
  t
  _ =
    st
      { ipac = _zero,
        feac = _zero,
        sd = t
      }

_STF_IPCI_PAM :: (ActusOps a, ActusNum a) => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_IPCI_PAM
  ct
  st@ContractStatePoly {..}
  t
  y_sd_t =
    let st' = _STF_IP_PAM ct st t y_sd_t
     in st'
          { nt = nt + ipac + y_sd_t * nt * ipnr
          }

_STF_RR_PAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> RiskFactorsPoly a -> b -> a -> a -> a -> ContractStatePoly a b
_STF_RR_PAM
  ct@ContractTermsPoly
    { ct_FEB = Just FEB_N,
      ct_FER = Just feeRate,
      ct_RRLF = Just rrlf,
      ct_RRLC = Just rrlc,
      ct_RRPC = Just rrpc,
      ct_RRPF = Just rrpf,
      ct_RRMLT = Just rrmlt,
      ct_RRSP = Just rrsp
    }
  st@ContractStatePoly {..}
  RiskFactorsPoly
    { ..
    }
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PRD_PAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
        delta_r = _min (_max (o_rf_RRMO * rrmlt + rrsp - ipnr) rrpf) rrpc
        ipnr' = _min (_max (ipnr + delta_r) rrlf) rrlc
     in st'
          { ipac = ipac + y_sd_t * ipnr * nt,
            feac = feac + y_sd_t * nt * feeRate,
            ipnr = ipnr',
            sd = t
          }
_STF_RR_PAM
  ct@ContractTermsPoly
    { ct_FER = Just feeRate,
      ct_RRLF = Just rrlf,
      ct_RRLC = Just rrlc,
      ct_RRPC = Just rrpc,
      ct_RRPF = Just rrpf,
      ct_RRMLT = Just rrmlt,
      ct_RRSP = Just rrsp,
      ct_CNTRL = cntrl
    }
  st@ContractStatePoly {..}
  RiskFactorsPoly
    { ..
    }
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PRD_PAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
        delta_r = _min (_max (o_rf_RRMO * rrmlt + rrsp - ipnr) rrpf) rrpc
        ipnr' = _min (_max (ipnr + delta_r) rrlf) rrlc
     in st'
          { ipac = ipac + y_sd_t * ipnr * nt,
            feac = (y_tfpminus_t / y_tfpminus_tfpplus) * _r cntrl * feeRate,
            ipnr = ipnr',
            sd = t
          }
_STF_RR_PAM _ st _ _ _ _ _ = st

_STF_RRF_PAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> ContractStatePoly a b
_STF_RRF_PAM
  ct@ContractTermsPoly
    { ct_RRNXT = rrnxt
    }
  st
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PRD_PAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
     in st'
          { ipnr = fromMaybe _zero rrnxt
          }

_STF_SC_PAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> RiskFactorsPoly a -> b -> a -> a -> a -> ContractStatePoly a b
_STF_SC_PAM
  ct@ContractTermsPoly
    { ct_SCEF = Just scef,
      ct_SCIED = Just scied
    }
  st@ContractStatePoly {..}
  RiskFactorsPoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PY_PAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus

        nsc' = case scef of
          SE_00M -> nsc
          SE_I00 -> nsc
          _      -> (o_rf_SCMO - scied) / scied

        isc' = case scef of
          SE_0N0 -> isc
          SE_00M -> isc
          SE_0NM -> isc
          _      -> (o_rf_SCMO - scied) / scied
     in st'
          { nsc = nsc',
            isc = isc'
          }
_STF_SC_PAM _ st _ _ _ _ _ = st

_STF_CE_PAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_CE_PAM = _STF_AD_PAM

-- Linear Amortiser (LAM)

_STF_IED_LAM :: (RoleSignOps a, Ord b) => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_IED_LAM
  ct@ContractTermsPoly
    { ct_NT = Just notionalPrincipal,
      ct_IPNR = Just nominalInterestRate,
      ct_CNTRL = cntrl
    }
  st
  t
  y_ipanx_t =
    let nt' = _r cntrl * notionalPrincipal
        ipcb' = interestCalculationBase ct
          where
            interestCalculationBase ContractTermsPoly {ct_IPCB = Just IPCB_NT} = nt'
            interestCalculationBase ContractTermsPoly {ct_IPCBA = Just ipcba}  = _r cntrl * ipcba
            interestCalculationBase _                                          = _zero
        ipac' = interestAccrued ct
          where
            interestAccrued ContractTermsPoly {ct_IPAC = Just ipac} = _r cntrl * ipac
            interestAccrued ContractTermsPoly {ct_IPANX = Just ipanx} | ipanx < t = y_ipanx_t * nt' * ipcb'
            interestAccrued _ = _zero
     in st
          { nt = nt',
            ipnr = nominalInterestRate,
            ipac = ipac',
            ipcb = ipcb',
            sd = t
          }
_STF_IED_LAM _ st _ _ = st

_STF_PR_LAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_PR_LAM
  ct@ContractTermsPoly
    { ct_CNTRL = cntrl,
      ct_FER = Just feeRate
    }
  st@ContractStatePoly {..}
  t
  y_sd_t =
    let nt' = nt - _r cntrl * (prnxt - _r cntrl * _max _zero (_abs prnxt - _abs nt))
        ipcb' = interestCalculationBase ct
          where
            interestCalculationBase ContractTermsPoly {ct_IPCB = Just IPCB_NTL} = ipcb
            interestCalculationBase _                                           = nt'
     in st
          { nt = nt',
            feac = feac + y_sd_t * nt * feeRate,
            ipcb = ipcb',
            ipac = ipac + ipnr * ipcb * y_sd_t,
            sd = t
          }
_STF_PR_LAM
  ct@ContractTermsPoly
    { ct_CNTRL = cntrl
    }
  st@ContractStatePoly {..}
  t
  y_sd_t =
    let nt' = nt - _r cntrl * (prnxt - _r cntrl * _max _zero (_abs prnxt - _abs nt))
        ipcb' = interestCalculationBase ct
          where
            interestCalculationBase ContractTermsPoly {ct_IPCB = Just IPCB_NTL} = ipcb
            interestCalculationBase _                                           = nt'
     in st
          { nt = nt',
            feac = feac,
            ipcb = ipcb',
            ipac = ipac + ipnr * ipcb * y_sd_t,
            sd = t
          }

_STF_MD_LAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_MD_LAM st t =
  st
    { nt = _zero,
      ipac = _zero,
      feac = _zero,
      ipcb = _zero,
      sd = t
    }

_STF_PP_LAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> RiskFactorsPoly a -> b -> a -> a -> a -> ContractStatePoly a b
_STF_PP_LAM
  ct
  st@ContractStatePoly {..}
  RiskFactorsPoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PY_LAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
        nt' = nt - pp_payoff
        ipcb' = interestCalculationBase ct
          where
            interestCalculationBase ContractTermsPoly {ct_IPCB = Just IPCB_NT} = nt'
            interestCalculationBase _                                          = ipcb
     in st'
          { nt = nt',
            ipcb = ipcb'
          }

_STF_PY_LAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> ContractStatePoly a b
_STF_PY_LAM
  ct@ContractTermsPoly
    { ct_FER = Just feeRate,
      ct_CNTRL = cntrl
    }
  st@ContractStatePoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let ipac' = ipac + y_sd_t * ipnr * ipcb
        feac' = feeAccrued ct
          where
            feeAccrued ContractTermsPoly {ct_FEB = Just FEB_N} = feac + y_sd_t * nt * feeRate
            feeAccrued _ = (y_tfpminus_t / y_tfpminus_tfpplus) * _r cntrl * feeRate
     in st
          { ipac = ipac',
            feac = feac',
            sd = t
          }
_STF_PY_LAM
  ct
  st@ContractStatePoly {..}
  t
  y_sd_t
  _
  _ =
    let ipac' = ipac + y_sd_t * ipnr * ipcb
        feac' = feeAccrued ct
          where
            feeAccrued ContractTermsPoly {ct_FEB = Just FEB_N} = feac
            feeAccrued _                                       = _zero
     in st
          { ipac = ipac',
            feac = feac',
            sd = t
          }

_STF_FP_LAM :: (ActusNum a, ActusOps a) => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_FP_LAM
  st@ContractStatePoly {..}
  t
  y_sd_t =
    st
      { ipac = ipac + y_sd_t * ipnr * ipcb,
        feac = _zero,
        sd = t
      }

_STF_PRD_LAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> ContractStatePoly a b
_STF_PRD_LAM = _STF_PY_LAM

_STF_IPCI_LAM :: (ActusOps a, ActusNum a) => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_IPCI_LAM
  ct
  st@ContractStatePoly {..}
  t
  y_sd_t =
    let st' = _STF_IP_PAM ct st t y_sd_t
        nt' = nt + ipac + y_sd_t * ipnr * ipcb
        ipcb' = interestCalculationBase ct
          where
            interestCalculationBase ContractTermsPoly {ct_IPCB = Just IPCB_NT} = nt'
            interestCalculationBase _                                          = ipcb
     in st'
          { nt = nt',
            ipcb = ipcb'
          }

_STF_IPCB_LAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> ContractStatePoly a b
_STF_IPCB_LAM
  ct
  st@ContractStatePoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PRD_LAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
     in st'
          { ipcb = nt
          }

_STF_RR_LAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> RiskFactorsPoly a -> b -> a -> a -> a -> ContractStatePoly a b
_STF_RR_LAM
  ct@ContractTermsPoly
    { ct_RRLF = Just rrlf,
      ct_RRLC = Just rrlc,
      ct_RRPC = Just rrpc,
      ct_RRPF = Just rrpf,
      ct_RRMLT = Just rrmlt,
      ct_RRSP = Just rrsp
    }
  st@ContractStatePoly {..}
  RiskFactorsPoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PRD_LAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
        delta_r = _min (_max (o_rf_RRMO * rrmlt + rrsp - ipnr) rrpf) rrpc
        ipnr' = _min (_max (ipnr + delta_r) rrlf) rrlc
     in st'
          { ipnr = ipnr'
          }
_STF_RR_LAM _ st _ _ _ _ _ = st

_STF_RRF_LAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> ContractStatePoly a b
_STF_RRF_LAM
  ct@ContractTermsPoly
    { ct_RRNXT = rrnxt
    }
  st
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PRD_LAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
     in st'
          { ipnr = fromMaybe _zero rrnxt
          }

_STF_SC_LAM :: (RoleSignOps a) => ContractTermsPoly a b -> ContractStatePoly a b -> RiskFactorsPoly a -> b -> a -> a -> a -> ContractStatePoly a b
_STF_SC_LAM
  ct@ContractTermsPoly
    { ct_SCCDD = Just sccdd,
      ct_SCEF = Just scef
    }
  st@ContractStatePoly {..}
  RiskFactorsPoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus =
    let st' = _STF_PY_LAM ct st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus
     in st'
          { nsc = if elem 'N' (show scef) then o_rf_SCMO / sccdd else nsc,
            isc = if elem 'I' (show scef) then o_rf_SCMO / sccdd else nsc
          }
_STF_SC_LAM _ st _ _ _ _ _ = st

-- Negative Amortizer (NAM)

_STF_PR_NAM :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_PR_NAM
  ct@ContractTermsPoly
    { ct_CNTRL = cntrl
    }
  st@ContractStatePoly {..}
  t
  y_sd_t =
    let st'@ContractStatePoly {ipac = ipac'} = _STF_PR_LAM ct st t y_sd_t
        nt' = nt - _r cntrl * r
          where
            ra = prnxt - _r cntrl * ipac'
            r = ra - _max _zero (ra - _abs nt)
        ipcb' = interestCalculationBase ct
          where
            interestCalculationBase ContractTermsPoly {ct_IPCB = Just IPCB_NT} = nt'
            interestCalculationBase _                                          = ipcb
     in st'
          { nt = nt',
            ipcb = ipcb'
          }

-- Annuity (ANN)

_STF_RR_ANN :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> RiskFactorsPoly a -> b -> a -> a -> a -> [a] -> ContractStatePoly a b
_STF_RR_ANN
  ct@ContractTermsPoly
    { ct_FER = feeRate,
      ct_RRLF = Just rrlf,
      ct_RRLC = Just rrlc,
      ct_RRPC = Just rrpc,
      ct_RRPF = Just rrpf,
      ct_RRMLT = Just rrmlt,
      ct_RRSP = Just rrsp,
      ct_CNTRL = cntrl
    }
  st@ContractStatePoly {..}
  RiskFactorsPoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus
  ti =
    let ipac' = ipac + y_sd_t * ipnr * ipcb
        feac' = feeAccrued ct
          where
            feeAccrued ContractTermsPoly {ct_FEB = Just FEB_N} = feac + y_sd_t * nt * fromMaybe _zero feeRate
            feeAccrued _ = (y_tfpminus_t / y_tfpminus_tfpplus) * _r cntrl * fromMaybe _zero feeRate
        ipnr' = _min (_max (ipnr + delta_r) rrlf) rrlc
          where
            delta_r = _min (_max (o_rf_RRMO * rrmlt + rrsp - ipnr) rrpf) rrpc
        prnxt' = annuity ipnr' ti
     in st
          { ipac = ipac',
            feac = feac',
            ipnr = ipnr',
            prnxt = prnxt',
            sd = t
          }
_STF_RR_ANN _ st _ _ _ _ _ _ = st

_STF_RRF_ANN :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> [a] -> ContractStatePoly a b
_STF_RRF_ANN
  ct@ContractTermsPoly
    { ct_FER = feeRate,
      ct_RRNXT = Just rrnxt,
      ct_CNTRL = cntrl
    }
  st@ContractStatePoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus
  ti =
    let ipac' = ipac + y_sd_t * ipnr * ipcb
        feac' = feeAccrued ct
          where
            feeAccrued ContractTermsPoly {ct_FEB = Just FEB_N} = feac + y_sd_t * nt * fromMaybe _zero feeRate
            feeAccrued _ = (y_tfpminus_t / y_tfpminus_tfpplus) * _r cntrl * fromMaybe _zero feeRate
        ipnr' = rrnxt
        prnxt' = annuity ipnr' ti
     in st
          { ipac = ipac',
            feac = feac',
            ipnr = ipnr',
            prnxt = prnxt',
            sd = t
          }
_STF_RRF_ANN _ st _ _ _ _ _ = st

_STF_PRF_ANN :: RoleSignOps a => ContractTermsPoly a b -> ContractStatePoly a b -> b -> a -> a -> a -> a -> [a] -> ContractStatePoly a b
_STF_PRF_ANN
  ct@ContractTermsPoly
    { ct_FER = feeRate,
      ct_CNTRL = cntrl
    }
  st@ContractStatePoly {..}
  t
  y_sd_t
  y_tfpminus_t
  y_tfpminus_tfpplus
  y_t
  ti =
    let ipac' = ipac + y_sd_t * ipnr * ipcb
        feac' = feeAccrued ct
          where
            feeAccrued ContractTermsPoly {ct_FEB = Just FEB_N} = feac + y_sd_t * nt * fromMaybe _zero feeRate
            feeAccrued _ = (y_tfpminus_t / y_tfpminus_tfpplus) * _r cntrl * fromMaybe _zero feeRate
        prnxt' = _r cntrl * frac * scale
          where
            scale = nt + ipac' + y_t * ipnr * nt
            frac = annuity ipnr ti
     in st
          { ipac = ipac',
            feac = feac',
            prnxt = prnxt',
            sd = t
          }
