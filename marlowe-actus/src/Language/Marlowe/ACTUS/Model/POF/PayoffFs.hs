{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module Language.Marlowe.ACTUS.Model.POF.PayoffFs where

import Language.Marlowe ( Observation, Value(SlotIntervalStart) )
import Language.Marlowe.ACTUS.Ops ( YearFractionOps(_y) )
import Language.Marlowe.ACTUS.Definitions.BusinessEvents
    ( EventType(IP, IED, MD, PP, PY, FP, PRD, TD))
import Language.Marlowe.ACTUS.Model.POF.PayoffModel
    ( _POF_IED_PAM,
      _POF_MD_PAM,
      _POF_PP_PAM,
      _POF_PY_PAM,
      _POF_FP_PAM,
      _POF_PRD_PAM,
      _POF_TD_PAM,
      _POF_IP_PAM )
import Language.Marlowe.ACTUS.Definitions.ContractTerms
    ( ContractTerms(..), ContractType(LAM, PAM) )
import Language.Marlowe.ACTUS.MarloweCompat
    ( useval, constnt, enum )


payoffFs :: EventType -> ContractTerms -> Integer -> (Value Observation)
payoffFs ev ContractTerms{..} t = 
    let __NT              = constnt _NT
        __PDIED           = constnt _PDIED
        __PYTP            = enum _PYTP
        __FEB             = enum _FEB
        __FER             = constnt _FER
        (__PPRD, __PTD  ) = (constnt _PPRD, constnt _PTD)
        (__PYRT, __cPYRT) = (constnt _PYRT, constnt _cPYRT)


        __o_rf_CURS       = useval "o_rf_CURS" t
        __o_rf_RRMO       = useval "o_rf_RRMO" t
        __pp_payoff       = useval "pp_payoff" t
        __nsc             = useval "nsc" t
        __nt              = useval "nt" t
        __isc             = useval "isc" t
        __ipac            = useval "ipac" t
        __feac            = useval "feac" t
        __fac             = useval "fac" t
        __ipnr            = useval "ipnr" t

        y_sd_t = _y _DCC (useval "sd" t) SlotIntervalStart undefined

    in case contractType of
        PAM -> case ev of
            IED -> _POF_IED_PAM __o_rf_CURS _CNTRL __NT __PDIED
            MD  -> _POF_MD_PAM __o_rf_CURS __nsc __nt __isc __ipac __feac
            PP  -> _POF_PP_PAM __o_rf_CURS __pp_payoff
            PY  -> _POF_PY_PAM __PYTP __o_rf_CURS __o_rf_RRMO __PYRT __cPYRT _CNTRL __nt __ipnr y_sd_t
            FP  -> _POF_FP_PAM __FEB __FER __o_rf_CURS _CNTRL __nt __fac y_sd_t
            PRD -> _POF_PRD_PAM __o_rf_CURS _CNTRL __PPRD __ipac __ipnr __nt y_sd_t
            TD -> _POF_TD_PAM __o_rf_CURS _CNTRL __PTD __ipac __ipnr __nt y_sd_t
            IP -> _POF_IP_PAM __o_rf_CURS __isc __ipac __ipnr __nt y_sd_t
            _  -> constnt 0
        LAM -> undefined

