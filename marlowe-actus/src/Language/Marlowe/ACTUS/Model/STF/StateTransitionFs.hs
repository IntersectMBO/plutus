{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.STF.StateTransitionFs
  (
    stateTransition
  )
where

import           Control.Monad.Reader
import           Data.Maybe                                             (fromMaybe, maybeToList)
import           Data.Time                                              (LocalTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents      (EventType (..), RiskFactorsMarlowe)
import           Language.Marlowe.ACTUS.Definitions.ContractState       (ContractStateMarlowe)
import           Language.Marlowe.ACTUS.Definitions.ContractTerms       (CT (..), ContractTerms, ContractTermsMarlowe,
                                                                         ContractTermsPoly (..))
import           Language.Marlowe.ACTUS.MarloweCompat                   (constnt, marloweTime)
import           Language.Marlowe.ACTUS.Model.STF.StateTransition       (CtxSTF (..))
import           Language.Marlowe.ACTUS.Model.STF.StateTransitionModel
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator (inf', sup')
import           Language.Marlowe.ACTUS.Ops                             (YearFractionOps (_y))

stateTransition :: EventType -> RiskFactorsMarlowe -> LocalTime -> LocalTime -> ContractStateMarlowe -> Reader (CtxSTF Double LocalTime) ContractStateMarlowe
stateTransition ev rf prevDate t st = reader stateTransitionFs'
  where
    stateTransitionFs' CtxSTF{ contractTerms = ct'@ContractTermsPoly {ct_MD = md, ct_DCC = Just dcc, ct_IPANX = Just ipanx}, ..} =
        stf ev (toMarlowe ct')
        where
          stf AD _ = _STF_AD_PAM st time y_sd_t
          stf IED ct@ContractTermsPoly {contractType = PAM} = _STF_IED_PAM ct st time y_ipanx_t
          stf IED ct@ContractTermsPoly {contractType = LAM} = _STF_IED_LAM ct st time y_ipanx_t
          stf IED ct@ContractTermsPoly {contractType = NAM} = _STF_IED_LAM ct st time y_ipanx_t
          stf IED ct@ContractTermsPoly {contractType = ANN} = _STF_IED_LAM ct st time y_ipanx_t
          stf PR ct@ContractTermsPoly {contractType = LAM} = _STF_PR_LAM ct st time y_sd_t
          stf PR ct@ContractTermsPoly {contractType = NAM} = _STF_PR_NAM ct st time y_sd_t
          stf PR ct@ContractTermsPoly {contractType = ANN} = _STF_PR_NAM ct st time y_sd_t
          stf MD ContractTermsPoly {contractType = PAM} = _STF_MD_PAM st time
          stf MD ContractTermsPoly {contractType = LAM} = _STF_MD_LAM st time
          stf MD ContractTermsPoly {contractType = NAM} = _STF_MD_LAM st time
          stf MD ContractTermsPoly {contractType = ANN} = _STF_MD_LAM st time
          stf PP ct@ContractTermsPoly {contractType = PAM} = _STF_PP_PAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PP ct@ContractTermsPoly {contractType = LAM} = _STF_PP_LAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PP ct@ContractTermsPoly {contractType = NAM} = _STF_PP_LAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PP ct@ContractTermsPoly {contractType = ANN} = _STF_PP_LAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PY ct@ContractTermsPoly {contractType = PAM} = _STF_PY_PAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PY ct@ContractTermsPoly {contractType = LAM} = _STF_PY_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PY ct@ContractTermsPoly {contractType = NAM} = _STF_PY_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PY ct@ContractTermsPoly {contractType = ANN} = _STF_PY_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf FP ContractTermsPoly {contractType = PAM} = _STF_FP_PAM st time y_sd_t
          stf FP ContractTermsPoly {contractType = LAM} = _STF_FP_LAM st time y_sd_t
          stf FP ContractTermsPoly {contractType = NAM} = _STF_FP_LAM st time y_sd_t
          stf FP ContractTermsPoly {contractType = ANN} = _STF_FP_LAM st time y_sd_t
          stf PRD ct@ContractTermsPoly {contractType = PAM} = _STF_PRD_PAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PRD ct@ContractTermsPoly {contractType = LAM} = _STF_PRD_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PRD ct@ContractTermsPoly {contractType = NAM} = _STF_PRD_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PRD ct@ContractTermsPoly {contractType = ANN} = _STF_PRD_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf TD _ = _STF_TD_PAM st time
          stf IP ct = _STF_IP_PAM ct st time y_sd_t
          stf IPCI ct@ContractTermsPoly {contractType = PAM} = _STF_IPCI_PAM ct st time y_sd_t
          stf IPCI ct@ContractTermsPoly {contractType = LAM} = _STF_IPCI_LAM ct st time y_sd_t
          stf IPCI ct@ContractTermsPoly {contractType = NAM} = _STF_IPCI_LAM ct st time y_sd_t
          stf IPCI ct@ContractTermsPoly {contractType = ANN} = _STF_IPCI_LAM ct st time y_sd_t
          stf IPCB ct@ContractTermsPoly {contractType = LAM} = _STF_IPCB_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf IPCB ct@ContractTermsPoly {contractType = NAM} = _STF_IPCB_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf IPCB ct@ContractTermsPoly {contractType = ANN} = _STF_IPCB_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf RR ct@ContractTermsPoly {contractType = PAM} = _STF_RR_PAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf RR ct@ContractTermsPoly {contractType = LAM} = _STF_RR_LAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf RR ct@ContractTermsPoly {contractType = NAM} = _STF_RR_LAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf RR ct@ContractTermsPoly {contractType = ANN} = _STF_RR_ANN ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus ti
          stf RRF ct@ContractTermsPoly {contractType = PAM} = _STF_RRF_PAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf RRF ct@ContractTermsPoly {contractType = LAM} = _STF_RRF_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf RRF ct@ContractTermsPoly {contractType = NAM} = _STF_RRF_LAM ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf RRF ct@ContractTermsPoly {contractType = ANN} = _STF_RRF_ANN ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus ti
          stf SC ct@ContractTermsPoly {contractType = PAM} = _STF_SC_PAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf PRF ct@ContractTermsPoly {contractType = ANN} = _STF_PRF_ANN ct st time y_sd_t y_tfpminus_t y_tfpminus_tfpplus y_t ti
          stf CE ContractTermsPoly {contractType = PAM} = _STF_CE_PAM st time y_sd_t
          stf SC ct@ContractTermsPoly {contractType = LAM} = _STF_SC_LAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf CE ContractTermsPoly {contractType = LAM} = _STF_CE_PAM st time y_sd_t
          stf SC ct@ContractTermsPoly {contractType = NAM} = _STF_SC_LAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf SC ct@ContractTermsPoly {contractType = ANN} = _STF_SC_LAM ct st rf time y_sd_t y_tfpminus_t y_tfpminus_tfpplus
          stf CE _ = _STF_AD_PAM st time y_sd_t
          stf _ _ = st

          time = marloweTime t

          tfp_minus = fromMaybe t (sup' fpSchedule t)
          tfp_plus = fromMaybe t (inf' fpSchedule t)
          tpr_plus = fromMaybe t (inf' prSchedule t)

          y_tfpminus_t = constnt $ _y dcc tfp_minus t md
          y_tfpminus_tfpplus = constnt $ _y dcc tfp_minus tfp_plus md
          y_ipanx_t = constnt $ _y dcc ipanx t md
          y_sd_t = constnt $ _y dcc prevDate t md
          y_t = constnt $ _y dcc t tpr_plus md

          prDates = prSchedule ++ maybeToList maturity
          prDatesAfterSd = filter (> t) prDates
          ti = zipWith (\tn tm -> constnt $ _y dcc tn tm md) prDatesAfterSd (tail prDatesAfterSd)
    stateTransitionFs' _ = st

toMarlowe :: ContractTerms -> ContractTermsMarlowe
toMarlowe ct =
  ContractTermsPoly
    { contractId = contractId ct,
      contractType = contractType ct,
      ct_CNTRL = ct_CNTRL ct,
      ct_CURS = ct_CURS ct,
      ct_IED = marloweTime <$> ct_IED ct,
      ct_DCC = ct_DCC ct,
      scfg = scfg ct,
      ct_SD = marloweTime $ ct_SD ct,
      ct_PRF = ct_PRF ct,
      ct_FECL = ct_FECL ct,
      ct_FEANX = marloweTime <$> ct_FEANX ct,
      ct_FEAC = constnt <$> ct_FEAC ct,
      ct_FEB = ct_FEB ct,
      ct_FER = constnt <$> ct_FER ct,
      ct_IPANX = marloweTime <$> ct_IPANX ct,
      ct_IPCL = ct_IPCL ct,
      ct_IPAC = constnt <$> ct_IPAC ct,
      ct_IPCED = marloweTime <$> ct_IPCED ct,
      ct_IPCBANX = marloweTime <$> ct_IPCBANX ct,
      ct_IPCBCL = ct_IPCBCL ct,
      ct_IPCB = ct_IPCB ct,
      ct_IPCBA = constnt <$> ct_IPCBA ct,
      ct_IPNR = constnt <$> ct_IPNR ct,
      ct_SCIP = constnt <$> ct_SCIP ct,
      ct_NT = constnt <$> ct_NT ct,
      ct_PDIED = constnt <$> ct_PDIED ct,
      ct_MD = marloweTime <$> ct_MD ct,
      ct_AD = marloweTime <$> ct_AD ct,
      ct_PRANX = marloweTime <$> ct_PRANX ct,
      ct_PRCL = ct_PRCL ct,
      ct_PRNXT = constnt <$> ct_PRNXT ct,
      ct_PRD = marloweTime <$> ct_PRD ct,
      ct_PPRD = constnt <$> ct_PPRD ct,
      ct_TD = marloweTime <$> ct_TD ct,
      ct_PTD = constnt <$> ct_PTD ct,
      ct_SCIED = constnt <$> ct_SCIED ct,
      ct_SCANX = marloweTime <$> ct_SCANX ct,
      ct_SCCL = ct_SCCL ct,
      ct_SCEF = ct_SCEF ct,
      ct_SCCDD = constnt <$> ct_SCCDD ct,
      ct_SCMO = ct_SCMO ct,
      ct_SCNT = constnt <$> ct_SCNT ct,
      ct_OPCL = ct_OPCL ct,
      ct_OPANX = marloweTime <$> ct_OPANX ct,
      ct_PYRT = constnt <$> ct_PYRT ct,
      ct_PYTP = ct_PYTP ct,
      ct_PPEF = ct_PPEF ct,
      ct_RRCL = ct_RRCL ct,
      ct_RRANX = marloweTime <$> ct_RRANX ct,
      ct_RRNXT = constnt <$> ct_RRNXT ct,
      ct_RRSP = constnt <$> ct_RRSP ct,
      ct_RRMLT = constnt <$> ct_RRMLT ct,
      ct_RRPF = constnt <$> ct_RRPF ct,
      ct_RRPC = constnt <$> ct_RRPC ct,
      ct_RRLC = constnt <$> ct_RRLC ct,
      ct_RRLF = constnt <$> ct_RRLF ct,
      ct_RRMO = ct_RRMO ct,
      enableSettlement = enableSettlement ct,
      constraints = constraints ct,
      collateralAmount = collateralAmount ct
    }
