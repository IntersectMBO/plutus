{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module Language.Marlowe.ACTUS.POF.PayoffLp where

import           Language.Marlowe
import           Language.Marlowe.ACTUS.Ops
import           Language.Marlowe.ACTUS.BusinessEvents
import           Language.Marlowe.ACTUS.POF.PayoffSpec
import           Language.Marlowe.ACTUS.ContractTerms
import           Language.Marlowe.ACTUS.MarloweCompat

payoffLp :: ContractTerms -> Integer -> (Value Observation)
payoffLp terms t = case terms of
    PamContractTerms {..} ->
        let y_sd_t  = _y _DCC (useval "sd" t) SlotIntervalStart undefined
            r_CNTRL = _r _CNTRL
        in  dispatchEvent t 0 $ \case
                IED -> _POF_IED_PAM (useval "o_rf_CURS" t)
                                r_CNTRL
                                (constnt _NT)
                                (constnt _PDIED)
                MD -> _POF_MD_PAM (useval "o_rf_CURS" t)
                                (useval "nsc" t)
                                (useval "nt" t)
                                (useval "isc" t)
                                (useval "ipac" t)
                                (useval "feac" t)
                PP -> _POF_PP_PAM (useval "o_rf_CURS" t) (useval "pp_payoff" t)
                PY -> _POF_PY_PAM (enum _PYTP)
                                (useval "o_rf_CURS" t)
                                (useval "o_rf_RRMO" t)
                                (constnt _PYRT)
                                (constnt _cPYRT)
                                r_CNTRL
                                (useval "nt" t)
                                (useval "ipnr" t)
                                y_sd_t
                FP -> _POF_FP_PAM (enum _FEB)
                                (constnt _FER)
                                (useval "o_rf_CURS" t)
                                r_CNTRL
                                (useval "nt" t)
                                (useval "fac" t)
                                y_sd_t
                PRD -> _POF_PRD_PAM (useval "o_rf_CURS" t)
                                r_CNTRL
                                (constnt _PPRD)
                                (useval "ipac" t)
                                (useval "ipnr" t)
                                (useval "nt" t)
                                y_sd_t
                TD -> _POF_TD_PAM (useval "o_rf_CURS" t)
                                r_CNTRL
                                (constnt _PTD)
                                (useval "ipac" t)
                                (useval "ipnr" t)
                                (useval "nt" t)
                                y_sd_t
                IP -> _POF_IP_PAM (useval "o_rf_CURS" t)
                                (useval "isc" t)
                                (useval "ipac" t)
                                (useval "ipnr" t)
                                (useval "nt" t)
                                y_sd_t
                _ -> constnt 0
    LamContractTerms {..} -> undefined





