{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransition
  (
    stateTransition
  , CtxSTF (..)
  )
where

import           Control.Monad.Reader                                   (Reader, ask)
import           Data.Maybe                                             (fromMaybe, maybeToList)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents      (EventType (..), RiskFactorsPoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (CT (..), ContractTermsPoly (..))
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (inf', sup')
import           Language.Marlowe.ACTUS.Ops                             (ActusOps (..), DateOps (..), RoleSignOps (..),
                                                                         YearFractionOps (_y))

data CtxSTF a b = CtxSTF
  { contractTerms :: ContractTermsPoly a b
  , fpSchedule    :: [b]
  , prSchedule    :: [b]
  , maturity      :: Maybe b
  }

-- |'stateTransition' updates the contract state based on the contract terms in the reader contrext
stateTransition :: (RoleSignOps a, YearFractionOps b a, DateOps b a, Ord b) =>
     EventType                                   -- ^ Event type
  -> RiskFactorsPoly a                           -- ^ Risk factors
  -> b                                           -- ^ Time
  -> ContractStatePoly a b                       -- ^ Contract state
  -> Reader (CtxSTF a b) (ContractStatePoly a b) -- ^ Updated contract state
stateTransition ev rf lt cs = ask >>= \CtxSTF{..} -> return $ stateTransition' ev rf contractTerms cs lt fpSchedule prSchedule maturity

stateTransition' :: (RoleSignOps a, YearFractionOps b a, DateOps b a, Ord b) =>
     EventType
  -> RiskFactorsPoly a
  -> ContractTermsPoly a b
  -> ContractStatePoly a b
  -> b
  -> [b]
  -> [b]
  -> Maybe b
  -> ContractStatePoly a b
stateTransition'
  ev
  RiskFactorsPoly {..}
  ct@ContractTermsPoly
    { ct_DCC = Just dayCountConvention,
      ct_IPANX = ipanx@(Just interestPaymentAnchor),
      ..
    }
  st@ContractStatePoly {..}
  t
  fpSchedule
  prSchedule
  m = stf ev ct
    where
      -- stf :: EventType -> ContractTerms -> ContractState
      stf AD _ = _STF_AD_PAM st t y_sd_t
      stf
        IED
        ContractTermsPoly
          { contractType = PAM,
            ct_NT = Just notionalPrincipal
          } = _STF_IED_PAM st t y_ipanx_t ct_IPNR ipanx ct_CNTRL ct_IPAC notionalPrincipal
      stf
        IED
        ContractTermsPoly
          { ct_NT = Just notionalPrincipal
          } = _STF_IED_LAM st t y_ipanx_t ct_IPNR ipanx ct_CNTRL ct_IPAC notionalPrincipal ct_IPCB ct_IPCBA
      stf PR ContractTermsPoly {contractType = LAM} = _STF_PR_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PR ContractTermsPoly {contractType = NAM} = _STF_PR_NAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PR ContractTermsPoly {contractType = ANN} = _STF_PR_NAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf MD _ = _STF_MD_PAM st t
      stf PP ContractTermsPoly {contractType = PAM} = _STF_PP_PAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PP ContractTermsPoly {contractType = LAM} = _STF_PP_LAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PP ContractTermsPoly {contractType = NAM} = _STF_PP_LAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PP ContractTermsPoly {contractType = ANN} = _STF_PP_LAM st t pp_payoff y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf PY ContractTermsPoly {contractType = PAM} = _STF_PY_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PY ContractTermsPoly {contractType = LAM} = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PY ContractTermsPoly {contractType = NAM} = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PY ContractTermsPoly {contractType = ANN} = _STF_PY_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf FP ContractTermsPoly {contractType = PAM} = _STF_FP_PAM st t y_sd_t
      stf FP ContractTermsPoly {contractType = LAM} = _STF_FP_LAM st t y_sd_t
      stf FP ContractTermsPoly {contractType = NAM} = _STF_FP_LAM st t y_sd_t
      stf FP ContractTermsPoly {contractType = ANN} = _STF_FP_LAM st t y_sd_t
      stf PRD ContractTermsPoly {contractType = PAM} = _STF_PRD_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PRD ContractTermsPoly {contractType = LAM} = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PRD ContractTermsPoly {contractType = NAM} = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf PRD ContractTermsPoly {contractType = ANN} = _STF_PRD_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf TD _ = _STF_TD_PAM st t
      stf IP _ = _STF_IP_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf IPCI ContractTermsPoly {contractType = PAM} = _STF_IPCI_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf IPCI ContractTermsPoly {contractType = LAM} = _STF_IPCI_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf IPCI ContractTermsPoly {contractType = NAM} = _STF_IPCI_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf IPCI ContractTermsPoly {contractType = ANN} = _STF_IPCI_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_IPCB
      stf IPCB ContractTermsPoly {contractType = LAM} = _STF_IPCB_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf IPCB ContractTermsPoly {contractType = NAM} = _STF_IPCB_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf IPCB ContractTermsPoly {contractType = ANN} = _STF_IPCB_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL
      stf
        RR
        ContractTermsPoly
          { contractType = PAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          } = _STF_RR_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrlf rrlc rrpc rrpf rrmlt rrsp o_rf_RRMO
      stf
        RR
        ContractTermsPoly
          { contractType = LAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          } = _STF_RR_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrlf rrlc rrpc rrpf rrmlt rrsp o_rf_RRMO
      stf
        RR
        ContractTermsPoly
          { contractType = NAM,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          } = _STF_RR_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrlf rrlc rrpc rrpf rrmlt rrsp o_rf_RRMO
      stf
        RR
        ContractTermsPoly
          { contractType = ANN,
            ct_RRLF = Just rrlf,
            ct_RRLC = Just rrlc,
            ct_RRPC = Just rrpc,
            ct_RRPF = Just rrpf,
            ct_RRMLT = Just rrmlt,
            ct_RRSP = Just rrsp
          } = _STF_RR_ANN st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrlf rrlc rrpc rrpf rrmlt rrsp o_rf_RRMO ti
      stf RRF ContractTermsPoly {contractType = PAM} = _STF_RRF_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_RRNXT
      stf RRF ContractTermsPoly {contractType = LAM} = _STF_RRF_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_RRNXT
      stf RRF ContractTermsPoly {contractType = NAM} = _STF_RRF_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_RRNXT
      stf
        RRF
        ContractTermsPoly
          { contractType = ANN,
            ct_RRNXT = Just rrnxt
          } = _STF_RRF_ANN st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL rrnxt ti
      stf PRF ContractTermsPoly {contractType = ANN} = _STF_PRF_ANN st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL ct_RRNXT y_t ti
      stf
        SC
        ContractTermsPoly
          { contractType = PAM,
            ct_SCEF = Just scef,
            ct_SCIED = Just scied
          } = _STF_SC_PAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL scef o_rf_SCMO scied
      stf
        SC
        ContractTermsPoly
          { contractType = LAM,
            ct_SCEF = Just scef,
            ct_SCCDD = Just sccdd
          } = _STF_SC_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL scef o_rf_SCMO sccdd
      stf
        SC
        ContractTermsPoly
          { contractType = NAM,
            ct_SCEF = Just scef,
            ct_SCCDD = Just sccdd
          } = _STF_SC_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL scef o_rf_SCMO sccdd
      stf
        SC
        ContractTermsPoly
          { contractType = ANN,
            ct_SCEF = Just scef,
            ct_SCCDD = Just sccdd
          } = _STF_SC_LAM st t y_sd_t y_tfpminus_t y_tfpminus_tfpplus ct_FEB feeRate ct_CNTRL scef o_rf_SCMO sccdd
      stf CE _ = _STF_CE_PAM st t y_sd_t
      stf _ _ = st

      feeRate = fromMaybe _zero ct_FER

      tfp_minus = fromMaybe t (sup' fpSchedule t)
      tfp_plus = fromMaybe t (inf' fpSchedule t)
      tpr_plus = fromMaybe t (inf' prSchedule t)

      y_sd_t = _y dayCountConvention sd t ct_MD
      y_tfpminus_t = _y dayCountConvention tfp_minus t ct_MD
      y_tfpminus_tfpplus = _y dayCountConvention tfp_minus tfp_plus ct_MD
      y_ipanx_t = _y dayCountConvention interestPaymentAnchor t ct_MD
      y_t = _y dayCountConvention t tpr_plus ct_MD

      prDates = prSchedule ++ maybeToList m
      prDatesAfterSd = filter (\d -> d > sd) prDates
      ti = zipWith (\tn tm -> _y dayCountConvention tn tm ct_MD) prDatesAfterSd (tail prDatesAfterSd)
stateTransition' _ _ _ s _ _ _ _ = s
