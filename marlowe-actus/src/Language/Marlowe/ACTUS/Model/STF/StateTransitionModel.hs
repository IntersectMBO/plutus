{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransitionModel where

import           Data.Maybe                                       (fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.ContractState (ContractStatePoly (ContractStatePoly, feac, ipac, ipcb, ipnr, isc, nsc, nt, prf, prnxt, sd, tmd))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms (CR, FEB (FEB_N), IPCB (..),
                                                                   SCEF (SE_00M, SE_0N0, SE_0NM, SE_I00))
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Annuity (annuity)
import           Language.Marlowe.ACTUS.Ops                       (ActusNum (..), ActusOps (..), DateOps (_lt),
                                                                   RoleSignOps (_r))
import           Prelude                                          hiding (Fractional, Num, (*), (+), (-), (/))

-- Principal at Maturity
_STF_AD_PAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_AD_PAM st@ContractStatePoly{..} t y_sd_t = st {
    ipac = ipac + y_sd_t * ipnr * nt,
    sd = t
}

_STF_IED_PAM :: (RoleSignOps a, DateOps b a) => ContractStatePoly a b -> b -> a -> Maybe a -> Maybe b -> CR -> Maybe a -> a -> ContractStatePoly a b
_STF_IED_PAM st t y_ipanx_t _IPNR _IPANX _CNTRL _IPAC _NT =
    let
        nt'                         = _r _CNTRL * _NT
        ipnr'                       = fromMaybe _zero _IPNR

        interestAccured (Just x) _ = x
        interestAccured _ (Just x) = _lt x t * y_ipanx_t * nt' * ipnr'
        interestAccured _ _        = _zero

        ipac'                      = interestAccured _IPAC _IPANX

    in st { nt = nt', ipnr = ipnr', ipac = ipac', sd = t }

_STF_MD_PAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_MD_PAM st t = st {
    nt = _zero,
    ipac = _zero,
    feac = _zero,
    sd = t
}

_STF_PP_PAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PP_PAM st@ContractStatePoly{..} t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let st' = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' {nt = nt - pp_payoff}

_STF_PY_PAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PY_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let
        ipac' = ipac + y_sd_t * ipnr * nt

        feac' = case _FEB of
            Just FEB_N -> feac + y_sd_t * nt * _FER
            _          -> _max _zero (y_tfpminus_t / y_tfpminus_tfpplus) * _r _CNTRL * _FER

    in st {ipac = ipac', feac = feac', sd = t}

_STF_FP_PAM :: (ActusNum a, ActusOps a) => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_FP_PAM st@ContractStatePoly{..} t y_sd_t = st {
    ipac = ipac + y_sd_t * ipnr * nt,
    feac = _zero,
    sd = t
}

_STF_PRD_PAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PRD_PAM = _STF_PY_PAM

_STF_TD_PAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_TD_PAM st t = st {
    nt = _zero,
    ipac = _zero,
    feac = _zero,
    ipnr = _zero,
    sd = t
}

_STF_IP_PAM :: (ActusOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> p1 -> p2 -> p3 -> a -> p4 -> ContractStatePoly a b
_STF_IP_PAM st@ContractStatePoly{..} t y_sd_t _ _ _FEB _FER _CNTRL =
    st {
        ipac = _zero,
        feac = y_sd_t * _FER * nt,
        sd = t
    }

_STF_IPCI_PAM :: (ActusOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_IPCI_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let
        st' = _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' {
        nt = nt + ipac + y_sd_t * nt * ipnr
    }

_STF_RR_PAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> a -> a -> a -> a -> a -> a -> a -> ContractStatePoly a b
_STF_RR_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO =
    let
        ipac' = ipac + y_sd_t * ipnr * nt
        feac'  =
          case _FEB of
            Just FEB_N -> feac + y_sd_t * nt * _FER
            _          -> (y_tfpminus_t / y_tfpminus_tfpplus) * _r _CNTRL * _FER

        st' = _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL

        delta_r = _min (_max (o_rf_RRMO * _RRMLT + _RRSP - ipnr) _RRPF) _RRPC

        ipnr' = _min (_max (ipnr + delta_r) _RRLF) _RRLC
    in st' {ipac = ipac', feac = feac', ipnr = ipnr', sd = t}

_STF_RRF_PAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe a -> ContractStatePoly a b
_STF_RRF_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRNXT =
    let
        st' = _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' {
        ipnr = fromMaybe _zero _RRNXT
    }

_STF_SC_PAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> SCEF -> a -> a -> ContractStatePoly a b
_STF_SC_PAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _SCEF o_rf_SCMO _SCIED =
    let
        st' = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL

        nsc' = case _SCEF of
            SE_00M -> nsc
            SE_I00 -> nsc
            _      -> (o_rf_SCMO - _SCIED) / _SCIED

        isc' = case _SCEF of
            SE_0N0 -> isc
            SE_00M -> isc
            SE_0NM -> isc
            _      -> (o_rf_SCMO - _SCIED) / _SCIED
    in st' {nsc = nsc', isc = isc'}

_STF_CE_PAM :: ActusNum a => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_CE_PAM = _STF_AD_PAM

-- Linear Amortiser (LAM)

_STF_IED_LAM :: (RoleSignOps a, Ord b) => ContractStatePoly a b -> b -> a -> Maybe a -> Maybe b -> CR -> Maybe a -> a -> Maybe IPCB -> Maybe a -> ContractStatePoly a b
_STF_IED_LAM st t y_ipanx_t (Just ipnr') _IPANX _CNTRL _IPAC _NT _IPCB _IPCBA =
    let
        nt'                         = _r _CNTRL * _NT

        interestCalculationBase (Just IPCB_NT) _                       = nt'
        interestCalculationBase _ (Just interestCalculationBaseAmount) = _r _CNTRL * interestCalculationBaseAmount
        interestCalculationBase _ _                                    = _zero

        ipcb' = interestCalculationBase _IPCB _IPCBA

        interestAccured (Just x) _         = _r _CNTRL * x
        interestAccured _ (Just x) | x < t = y_ipanx_t * nt' * ipcb'
        interestAccured _ _                = _zero

        ipac' = interestAccured _IPAC _IPANX
    in st { nt = nt', ipnr = ipnr', ipac = ipac', ipcb = ipcb', sd = t }
_STF_IED_LAM st _ _ Nothing _ _ _ _ _ _ = st

_STF_PR_LAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_PR_LAM st@ContractStatePoly{..} t y_sd_t _ _ _FEB _FER _CNTRL _IPCB =
    let
        nt' = nt - _r _CNTRL * (prnxt - _r _CNTRL * _max _zero (_abs prnxt - _abs nt))

        -- feac' = case _FEB of
        --     Just FEB_N -> feac + y_sd_t * nt * _FER
        --     _          -> (_max _zero (y_tfpminus_t / y_tfpminus_tfpplus)) * _r _CNTRL * _FER
        feac' = feac + y_sd_t * nt * _FER

        ipcb' = case _IPCB of
            Just IPCB_NTL -> ipcb
            _             -> nt'

        ipac' = ipac + ipnr * ipcb * y_sd_t

    in st {nt = nt', feac = feac', ipcb = ipcb', ipac = ipac', sd = t}

_STF_MD_LAM :: ActusOps a => ContractStatePoly a b -> b -> ContractStatePoly a b
_STF_MD_LAM st t = st {
    nt = _zero,
    ipac = _zero,
    feac = _zero,
    ipcb = _zero,
    sd = t
}

_STF_PP_LAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_PP_LAM st@ContractStatePoly{..} t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB =
    let
        st' = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
        nt' = nt - pp_payoff
        ipcb' = case _IPCB of
            Just IPCB_NT -> nt'
            _            -> ipcb
    in st' {nt = nt', ipcb = ipcb'}

_STF_PY_LAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PY_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let
        ipac' = ipac + y_sd_t * ipnr * ipcb

        feac' = case _FEB of
            Just FEB_N -> feac + y_sd_t * nt * _FER
            _          -> (y_tfpminus_t / y_tfpminus_tfpplus) * _r _CNTRL * _FER

    in st {ipac = ipac', feac = feac', sd = t}

_STF_FP_LAM :: (ActusNum a, ActusOps a) => ContractStatePoly a b -> b -> a -> ContractStatePoly a b
_STF_FP_LAM st@ContractStatePoly{..} t y_sd_t = st {
    ipac = ipac + y_sd_t * ipnr * ipcb,
    feac = _zero,
    sd = t
}

_STF_PRD_LAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_PRD_LAM = _STF_PY_LAM

_STF_IPCI_LAM :: (ActusOps a, ActusNum a) => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_IPCI_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB =
    let
        st' = _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
        nt' = nt + ipac + y_sd_t * ipnr * ipcb
        ipcb' = case _IPCB of
            Just IPCB_NT -> nt'
            _            -> ipcb
    in st' {nt = nt', ipcb = ipcb'}

_STF_IPCB_LAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> ContractStatePoly a b
_STF_IPCB_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL =
    let st' = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' { ipcb = nt }

_STF_RR_LAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> a -> a -> a -> a -> a -> a -> a -> ContractStatePoly a b
_STF_RR_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO =
    let
        st' = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL

        delta_r = _min (_max (o_rf_RRMO * _RRMLT + _RRSP - ipnr) _RRPF) _RRPC

        ipnr' = _min (_max (ipnr + delta_r) _RRLF) _RRLC
    in st' {ipnr = ipnr'}

_STF_RRF_LAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe a -> ContractStatePoly a b
_STF_RRF_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRNXT =
    let st' = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL
    in st' { ipnr = fromMaybe _zero _RRNXT }

_STF_SC_LAM :: (Show c, RoleSignOps a)  => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> c -> a -> a -> ContractStatePoly a b
_STF_SC_LAM st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _SCEF o_rf_SCMO _SCCDD =
    let
        st' = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL

        nsc' =
          if elem 'N' (show _SCEF) then
            o_rf_SCMO / _SCCDD
          else
            nsc

        isc' =
          if elem 'I' (show _SCEF) then
            o_rf_SCMO / _SCCDD
          else
            nsc
    in st' {nsc = nsc', isc = isc'}

-- Negative Amortizer (NAM)

_STF_PR_NAM :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> a -> Maybe FEB -> a -> CR -> Maybe IPCB -> ContractStatePoly a b
_STF_PR_NAM st@ContractStatePoly{..} t _ y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB =
    -- let
    --     st'@ContractStatePoly{ ipac = ipac' } =
    --       _STF_PR_LAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB
    --
    --     nt' = nt - prnxt - ipac'
    -- in st' { nt = nt' }
    let
      st'@ContractStatePoly{ ipac = ipac' } = _STF_PR_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _IPCB
      ra  = prnxt - _r _CNTRL * ipac'
      r   = ra - _max _zero (ra - _abs nt)
      nt' = nt - _r _CNTRL * r

      -- ACTUS implementation
      ipcb' = case _IPCB of
          Just IPCB_NT -> nt'
          _            -> ipcb

      -- -- Java implementation
      -- ipcb' = nt'

    in st'{ nt = nt', ipcb = ipcb' }

-- Annuity (ANN)

_STF_RR_ANN :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> a -> a -> a -> a -> a -> a -> a -> [a] -> ContractStatePoly a b
_STF_RR_ANN st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRLF _RRLC _RRPC _RRPF _RRMLT _RRSP o_rf_RRMO ti =
  let ipac' = ipac + y_sd_t * ipnr * ipcb

      feac' = case _FEB of
        Just FEB_N -> feac + y_sd_t * nt * _FER
        _          -> y_tfpminus_t / y_tfpminus_tfpplus * _r _CNTRL * _FER

      delta_r = _min (_max (o_rf_RRMO * _RRMLT + _RRSP - ipnr) _RRPF) _RRPC

      ipnr' = _min (_max (ipnr + delta_r) _RRLF) _RRLC

      prnxt' = annuity ipnr' ti

   in st
        { ipac = ipac',
          feac = feac',
          ipnr = ipnr',
          prnxt = prnxt',
          sd = t
        }

_STF_RRF_ANN :: RoleSignOps a => ContractStatePoly a b -> b -> a -> a -> a -> Maybe FEB -> a -> CR -> a -> [a] -> ContractStatePoly a b
_STF_RRF_ANN st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRNXT ti =
  let ipac' = ipac + y_sd_t * ipnr * ipcb

      feac' = case _FEB of
        Just FEB_N -> feac + y_sd_t * nt * _FER
        _          -> y_tfpminus_t / y_tfpminus_tfpplus * _r _CNTRL * _FER


      ipnr' = _RRNXT

      prnxt' = annuity ipnr' ti

   in st
        { ipac = ipac',
          feac = feac',
          ipnr = ipnr',
          prnxt = prnxt',
          sd = t
        }

_STF_PRF_ANN :: RoleSignOps a => ContractStatePoly a b -> b -> a-> a-> a -> Maybe FEB -> a -> CR -> Maybe a -> a -> [a] -> ContractStatePoly a b
_STF_PRF_ANN st@ContractStatePoly{..} t y_sd_t y_tfpminus_t y_tfpminus_tfpplus _FEB _FER _CNTRL _RRNXT y_t ti =
  let accruedInterest = ipac + y_sd_t * ipnr * ipcb

      feeAccrued = case _FEB of
        Just FEB_N -> feac + y_sd_t * nt * _FER
        _          -> y_tfpminus_t / y_tfpminus_tfpplus * _r _CNTRL * _FER

      scale = nt + accruedInterest + y_t*ipnr*nt
      frac = annuity ipnr ti

      nextPrincipalRedemptionPayment = _r _CNTRL * frac * scale
      statusDate = t

   in st
        { ipac = accruedInterest,
          feac = feeAccrued,
          prnxt = nextPrincipalRedemptionPayment,
          sd = statusDate
        }
