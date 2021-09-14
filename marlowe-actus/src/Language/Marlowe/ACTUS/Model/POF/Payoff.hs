{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.POF.Payoff where

import           Data.Time                                         (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType (..), RiskFactors, RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState  (ContractState, ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  (CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Model.POF.PayoffModel
import           Language.Marlowe.ACTUS.Ops                        (YearFractionOps (_y))

payoff :: EventType -> RiskFactors -> ContractTerms -> ContractState -> LocalTime -> Double
-- IED
payoff
  IED
  RiskFactorsPoly {..}
  ContractTerms
    { ct_NT = Just notionalPrincipal,
      ct_PDIED = Just pdied,
      ct_CNTRL = cntrl
    }
  _
  _ = _POF_IED_PAM o_rf_CURS cntrl notionalPrincipal pdied
-- PR
payoff
  PR
  RiskFactorsPoly {..}
  ContractTerms
    { contractType = LAM,
      ct_CNTRL = cntrl
    }
  ContractStatePoly {..}
  _ = _POF_PR_LAM o_rf_CURS cntrl nt nsc prnxt
payoff
  PR
  RiskFactorsPoly {..}
  ContractTerms
    { contractType = NAM,
      ct_DCC = Just dayCountConvention,
      ct_CNTRL = cntrl,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_PR_NAM o_rf_CURS cntrl nsc prnxt ipac y_sd_t ipnr ipcb nt
payoff
  PR
  RiskFactorsPoly {..}
  ContractTerms
    { contractType = ANN,
      ct_DCC = Just dayCountConvention,
      ct_CNTRL = cntrl,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_PR_NAM o_rf_CURS cntrl nsc prnxt ipac y_sd_t ipnr ipcb nt
-- MD
payoff MD RiskFactorsPoly {..} _ ContractStatePoly {..} _ = _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
-- PP
payoff PP RiskFactorsPoly {..} _ _ _ = _POF_PP_PAM o_rf_CURS pp_payoff
-- PY
payoff
  PY
  RiskFactorsPoly {..}
  ContractTerms
    { ct_PYTP = Just pytp,
      ct_PYRT = Just pyrt,
      ct_DCC = Just dayCountConvention,
      ct_CNTRL = cntrl,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_PY_PAM pytp o_rf_CURS o_rf_RRMO pyrt cntrl nt ipnr y_sd_t
-- FP
payoff
  FP
  RiskFactorsPoly {..}
  ContractTerms
    { ct_DCC = Just dayCountConvention,
      ct_CNTRL = cntrl,
      ct_FEB = Just feb,
      ct_FER = Just fer,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_FP_PAM feb fer o_rf_CURS cntrl nt feac y_sd_t
-- PRD
payoff
  PRD
  RiskFactorsPoly {..}
  ContractTerms
    { contractType = PAM,
      ct_DCC = Just dayCountConvention,
      ct_CNTRL = cntrl,
      ct_PPRD = Just pprd,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_PRD_PAM o_rf_CURS cntrl pprd ipac ipnr nt y_sd_t
payoff
  PRD
  RiskFactorsPoly {..}
  ContractTerms
    { ct_DCC = Just dayCountConvention,
      ct_CNTRL = cntrl,
      ct_PPRD = Just pprd,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_PRD_LAM o_rf_CURS cntrl pprd ipac ipnr ipcb y_sd_t
-- TD
payoff
  TD
  RiskFactorsPoly {..}
  ContractTerms
    { contractType = PAM,
      ct_DCC = Just dayCountConvention,
      ct_CNTRL = cntrl,
      ct_PTD = Just ptd,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_TD_PAM o_rf_CURS cntrl ptd ipac ipnr nt y_sd_t
payoff
  TD
  RiskFactorsPoly {..}
  ContractTerms
    { ct_DCC = Just dayCountConvention,
      ct_CNTRL = cntrl,
      ct_PTD = Just ptd,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_TD_LAM o_rf_CURS cntrl ptd ipac ipnr ipcb y_sd_t
-- IP
payoff
  IP
  RiskFactorsPoly {..}
  ContractTerms
    { contractType = PAM,
      ct_DCC = Just dayCountConvention,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_IP_PAM o_rf_CURS isc ipac ipnr nt y_sd_t
payoff
  IP
  RiskFactorsPoly {..}
  ContractTerms
    { ct_DCC = Just dayCountConvention,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_IP_LAM o_rf_CURS isc ipac ipnr ipcb y_sd_t
payoff _ _ _ _ _ = 0.0
