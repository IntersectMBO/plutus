{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.POF.Payoff
  ( payoff )
where

import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType (..), RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState  (ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  (CT (..), ContractTermsPoly (..))
import           Language.Marlowe.ACTUS.Model.POF.PayoffModel
import           Language.Marlowe.ACTUS.Ops                        (ActusOps (..), RoleSignOps (..),
                                                                    YearFractionOps (_y))

-- |'payoff' function for ACTUS contracts
payoff :: (RoleSignOps a, YearFractionOps b a) =>
     EventType             -- ^ Event type
  -> RiskFactorsPoly a     -- ^ Risk factors
  -> ContractTermsPoly a b -- ^ Contract terms (constant)
  -> ContractStatePoly a b -- ^ Contract state
  -> b                     -- ^ Time
  -> a                     -- ^ Payoff amount
-- IED
payoff
  IED
  RiskFactorsPoly {..}
  ContractTermsPoly
    { ct_NT = Just notionalPrincipal,
      ct_PDIED = Just pdied,
      ct_CNTRL = cntrl
    }
  _
  _ = _POF_IED_PAM o_rf_CURS cntrl notionalPrincipal pdied
payoff
  IED
  RiskFactorsPoly {..}
  ContractTermsPoly
    { ct_NT = Just notionalPrincipal,
      ct_CNTRL = cntrl
    }
  _
  _ = _POF_IED_PAM o_rf_CURS cntrl notionalPrincipal _zero
-- PR
payoff
  PR
  RiskFactorsPoly {..}
  ContractTermsPoly
    { contractType = LAM,
      ct_CNTRL = cntrl
    }
  ContractStatePoly {..}
  _ = _POF_PR_LAM o_rf_CURS cntrl nt nsc prnxt
payoff
  PR
  RiskFactorsPoly {..}
  ContractTermsPoly
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
  ContractTermsPoly
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
payoff
  MD
  _
  ContractTermsPoly
    { contractType = OPTNS
    }
  _
  _ = _POF_MD_OPTNS
payoff MD RiskFactorsPoly {..} _ ContractStatePoly {..} _ = _POF_MD_PAM o_rf_CURS nsc nt isc ipac feac
-- PP
payoff PP RiskFactorsPoly {..} _ _ _ = _POF_PP_PAM o_rf_CURS pp_payoff
-- PY
payoff
  PY
  RiskFactorsPoly {..}
  ContractTermsPoly
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
  ContractTermsPoly
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
  ContractTermsPoly
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
  _
  ContractTermsPoly
    { contractType = STK,
      ct_CNTRL = cntrl,
      ct_PPRD = Just pprd
    }
  _
  _ = _POF_PRD_STK cntrl pprd
payoff
  PRD
  _
  ContractTermsPoly
    { contractType = OPTNS,
      ct_CNTRL = cntrl,
      ct_PPRD = Just pprd
    }
  _
  _ = _POF_PRD_STK cntrl pprd
payoff
  PRD
  _
  ContractTermsPoly
    { contractType = FUTUR,
      ct_CNTRL = cntrl,
      ct_PPRD = Just pprd
    }
  _
  _ = _POF_PRD_STK cntrl pprd
payoff
  PRD
  RiskFactorsPoly {..}
  ContractTermsPoly
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
  ContractTermsPoly
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
  _
  ContractTermsPoly
    { contractType = STK,
      ct_CNTRL = cntrl,
      ct_PTD = Just ptd
    }
  _
  _ = _POF_TD_STK cntrl ptd
payoff
  TD
  RiskFactorsPoly {..}
  ContractTermsPoly
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
  ContractTermsPoly
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
  ContractTermsPoly
    { ct_DCC = Just dayCountConvention,
      ct_MD = md
    }
  ContractStatePoly {..}
  t =
    let y_sd_t = _y dayCountConvention sd t md
     in _POF_IP_LAM o_rf_CURS isc ipac ipnr ipcb y_sd_t
-- DV
payoff
  DV
  RiskFactorsPoly {..}
  ContractTermsPoly
    { contractType = STK,
      ct_CNTRL = cntrl
    }
  _
  _ = _POF_DV_STK cntrl o_rf_CURS pp_payoff
-- STD
payoff
  STD
  RiskFactorsPoly {..}
  ContractTermsPoly
    { contractType = OPTNS,
      ct_CNTRL = cntrl
    }
  ContractStatePoly
    { xa = Just exerciseAmount}
  _ = _POF_STD_OPTNS cntrl o_rf_CURS exerciseAmount
payoff
  STD
  RiskFactorsPoly {..}
  ContractTermsPoly
    { contractType = FUTUR,
      ct_CNTRL = cntrl
    }
  ContractStatePoly
    { xa = Just exerciseAmount}
  _ = _POF_STD_OPTNS cntrl o_rf_CURS exerciseAmount
payoff _ _ _ _ _ = _zero
