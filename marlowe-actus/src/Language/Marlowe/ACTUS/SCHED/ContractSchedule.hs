{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.SCHED.ContractSchedule where

import Language.Marlowe.ACTUS.ContractTerms
    ( ContractTerms(..), ContractType(LAM, PAM) )
import Language.Marlowe.ACTUS.BusinessEvents
    ( EventType(SC, IED, MD, PP, PY, FP, PRD, TD, IP, IPCI, RR, RRF) )
import Language.Marlowe.ACTUS.Schedule ( ShiftedDay )
import Language.Marlowe.ACTUS.SCHED.ContractScheduleModel
    ( _SCHED_IED_PAM,
      _SCHED_MD_PAM,
      _SCHED_PP_PAM,
      _SCHED_PY_PAM,
      _SCHED_FP_PAM,
      _SCHED_PRD_PAM,
      _SCHED_TD_PAM,
      _SCHED_IP_PAM,
      _SCHED_IPCI_PAM,
      _SCHED_RR_PAM,
      _SCHED_RRF_PAM,
      _SCHED_SC_PAM )


schedule :: EventType -> ContractTerms -> Maybe [ShiftedDay]
schedule ev ContractTerms {..} = case contractType of
    PAM -> case ev of
        IED  -> _SCHED_IED_PAM scfg _IED
        MD   -> _SCHED_MD_PAM scfg _MD
        PP   -> _SCHED_PP_PAM scfg _PREF _OPCL _IED _OPANX _MD
        PY   -> _SCHED_PY_PAM scfg _PYTP _PREF _OPCL _IED _OPANX _MD
        FP   -> _SCHED_FP_PAM scfg _FER _FECL _IED _FEANX _MD
        PRD  -> _SCHED_PRD_PAM scfg _PRD
        TD   -> _SCHED_TD_PAM scfg _TD
        IP   -> _SCHED_IP_PAM scfg _IPNR _IED _IPANX _IPCL _IPCED _MD
        IPCI -> _SCHED_IPCI_PAM scfg _IED _IPANX _IPCL _IPCED
        RR   -> _SCHED_RR_PAM scfg _IED _SD _RRANX _RRCL _RRNXT _MD
        RRF  -> _SCHED_RRF_PAM scfg _IED _RRANX _RRCL _MD
        SC   -> _SCHED_SC_PAM scfg _IED _SCEF _SCANX _SCCL _MD
        _    -> Nothing
    LAM -> undefined
