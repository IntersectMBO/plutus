{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule where

import           Data.Maybe                                                 (fromJust, fromMaybe)

import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (FP, IED, IP, IPCB, IPCI, MD, PP, PR, PRD, PY, RR, RRF, SC, TD))
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractStatePoly (tmd))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (CT (LAM, NAM, PAM), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_LAM, _INIT_NAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (inf, sup)


schedule :: EventType -> ContractTerms -> Maybe [ShiftedDay]
schedule ev ct@ContractTerms {..} = case contractType of
    PAM -> case ev of
        IED  -> _SCHED_IED_PAM scfg (fromJust ct_IED)
        MD   -> _SCHED_MD_PAM scfg (fromJust ct_MD)
        PP   -> _SCHED_PP_PAM scfg (fromJust ct_PPEF) ct_OPCL (fromJust ct_IED) ct_OPANX (fromJust ct_MD)
        PY   -> _SCHED_PY_PAM scfg (fromJust ct_PYTP) (fromJust ct_PPEF) ct_OPCL (fromJust ct_IED) ct_OPANX (fromJust ct_MD)
        FP   -> _SCHED_FP_PAM scfg (fromJust ct_FER) ct_FECL (fromJust ct_IED) ct_FEANX (fromJust ct_MD)
        PRD  -> _SCHED_PRD_PAM scfg (fromJust ct_PRD)
        TD   -> _SCHED_TD_PAM scfg (fromJust ct_TD)
        IP   -> _SCHED_IP_PAM scfg ct_IPNR (fromJust ct_IED) ct_IPANX ct_IPCL ct_IPCED (fromJust ct_MD)
        IPCI -> _SCHED_IPCI_PAM scfg (fromJust ct_IED) ct_IPANX ct_IPCL ct_IPCED
        RR   -> _SCHED_RR_PAM scfg (fromJust ct_IED) ct_SD ct_RRANX ct_RRCL ct_RRNXT (fromJust ct_MD)
        RRF  -> _SCHED_RRF_PAM scfg (fromJust ct_IED) ct_RRANX ct_RRCL (fromJust ct_MD)
        SC   -> _SCHED_SC_PAM scfg (fromJust ct_IED) (fromJust ct_SCEF) ct_SCANX ct_SCCL (fromJust ct_MD)
        _    -> Nothing
    LAM ->
      let
        -- Need LAM state initialization since MD schedule is Tmd0 which may consist of other terms
        -- Also cannot call initializeState directly without cyclical imports
        t0                 = ct_SD
        fpSchedule         = schedule FP ct
        tfp_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< fpSchedule)
        tfp_plus           = fromMaybe t0 $ calculationDay <$> ((\sc -> inf sc t0) =<< fpSchedule)
        ipSchedule         = schedule IP ct
        tminus             = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< ipSchedule)
        prSchedule         = schedule PR ct
        tpr_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< prSchedule)
        _tmd = tmd $ _INIT_LAM ct_SD tminus tpr_minus tfp_minus tfp_plus ct
      in case ev of
        IED  -> _SCHED_IED_LAM scfg (fromJust ct_IED)
        PR   -> _SCHED_PR_LAM scfg ct_PRCL (fromJust ct_IED) ct_PRANX _tmd
        MD   -> _SCHED_MD_LAM scfg _tmd
        PP   -> _SCHED_PP_LAM scfg (fromJust ct_PPEF) ct_OPCL (fromJust ct_IED) ct_OPANX _tmd
        PY   -> _SCHED_PY_LAM scfg (fromJust ct_PYTP) (fromJust ct_PPEF) ct_OPCL (fromJust ct_IED) ct_OPANX _tmd
        FP   -> _SCHED_FP_LAM scfg (fromJust ct_FER) ct_FECL (fromJust ct_IED) ct_FEANX _tmd
        PRD  -> _SCHED_PRD_LAM scfg (fromJust ct_PRD)
        TD   -> _SCHED_TD_LAM scfg (fromJust ct_TD)
        IP   -> _SCHED_IP_LAM scfg ct_IPNR (fromJust ct_IED) ct_IPANX ct_IPCL ct_IPCED _tmd
        IPCI -> _SCHED_IPCI_LAM scfg (fromJust ct_IED) ct_IPANX ct_IPCL ct_IPCED
        IPCB -> _SCHED_IPCB_LAM scfg (fromJust ct_IED) ct_IPCB ct_IPCBCL ct_IPCBANX _tmd
        RR   -> _SCHED_RR_LAM scfg (fromJust ct_IED) ct_SD ct_RRANX ct_RRCL ct_RRNXT _tmd
        RRF  -> _SCHED_RRF_LAM scfg (fromJust ct_IED) ct_RRANX ct_RRCL _tmd
        SC   -> _SCHED_SC_LAM scfg (fromJust ct_IED) (fromJust ct_SCEF) ct_SCANX ct_SCCL _tmd
        _    -> Nothing
    NAM ->
      -- Same as LAM - need to calculate Tmd0
      -- TODO: refactor for LAM and NAM
      let
        t0                 = ct_SD
        fpSchedule         = schedule FP ct
        tfp_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< fpSchedule)
        tfp_plus           = fromMaybe t0 $ calculationDay <$> ((\sc -> inf sc t0) =<< fpSchedule)
        ipSchedule         = schedule IP ct
        tminus             = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< ipSchedule)
        prSchedule         = schedule PR ct
        tpr_minus          = fromMaybe t0 $ calculationDay <$> ((\sc -> sup sc t0) =<< prSchedule)
        _tmd = tmd $ _INIT_NAM ct_SD tminus tpr_minus tfp_minus tfp_plus ct
      in case ev of
        IED  -> _SCHED_IED_NAM scfg (fromJust ct_IED)
        PR   -> _SCHED_PR_NAM scfg ct_PRCL (fromJust ct_IED) ct_PRANX _tmd
        MD   -> _SCHED_MD_NAM scfg _tmd
        PP   -> _SCHED_PP_NAM scfg (fromJust ct_PPEF) ct_OPCL (fromJust ct_IED) ct_OPANX _tmd
        PY   -> _SCHED_PY_NAM scfg (fromJust ct_PYTP) (fromJust ct_PPEF) ct_OPCL (fromJust ct_IED) ct_OPANX _tmd
        FP   -> _SCHED_FP_NAM scfg (fromJust ct_FER) ct_FECL (fromJust ct_IED) ct_FEANX _tmd
        PRD  -> _SCHED_PRD_NAM scfg (fromJust ct_PRD)
        TD   -> _SCHED_TD_NAM scfg (fromJust ct_TD)
        IP   -> _SCHED_IP_NAM scfg (fromJust ct_IED) ct_PRCL ct_PRANX ct_IPCED ct_IPANX ct_IPCL _tmd
        IPCI -> _SCHED_IPCI_NAM scfg (fromJust ct_IED) ct_IPANX ct_IPCL ct_IPCED
        IPCB -> _SCHED_IPCB_NAM scfg (fromJust ct_IED) ct_IPCB ct_IPCBCL ct_IPCBANX _tmd
        RR   -> _SCHED_RR_NAM scfg (fromJust ct_IED) ct_SD ct_RRANX ct_RRCL ct_RRNXT _tmd
        RRF  -> _SCHED_RRF_NAM scfg (fromJust ct_IED) ct_RRANX ct_RRCL _tmd
        SC   -> _SCHED_SC_NAM scfg (fromJust ct_IED) (fromJust ct_SCEF) ct_SCANX ct_SCCL _tmd
        _    -> Nothing
