{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule where

import           Language.Marlowe.ACTUS.Definitions.BusinessEvents        (EventType (FP, IED, IP, IPCI, MD, PP, PRD, PY, RR, RRF, SC, TD))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms         (ContractTerms (..), ContractType (LAM, PAM))
import           Language.Marlowe.ACTUS.Definitions.Schedule              (ShiftedDay)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel (_SCHED_FP_PAM, _SCHED_IED_PAM,
                                                                           _SCHED_IPCI_PAM, _SCHED_IP_PAM,
                                                                           _SCHED_MD_PAM, _SCHED_PP_PAM, _SCHED_PRD_PAM,
                                                                           _SCHED_PY_PAM, _SCHED_RRF_PAM, _SCHED_RR_PAM,
                                                                           _SCHED_SC_PAM, _SCHED_TD_PAM)


schedule :: EventType -> ContractTerms -> Maybe [ShiftedDay]
schedule ev ContractTerms {..} = case contractType of
    PAM -> case ev of
        IED  -> _SCHED_IED_PAM scfg ct_IED
        MD   -> _SCHED_MD_PAM scfg ct_MD
        PP   -> _SCHED_PP_PAM scfg ct_PREF ct_OPCL ct_IED ct_OPANX ct_MD
        PY   -> _SCHED_PY_PAM scfg ct_PYTP ct_PREF ct_OPCL ct_IED ct_OPANX ct_MD
        FP   -> _SCHED_FP_PAM scfg ct_FER ct_FECL ct_IED ct_FEANX ct_MD
        PRD  -> _SCHED_PRD_PAM scfg ct_PRD
        TD   -> _SCHED_TD_PAM scfg ct_TD
        IP   -> _SCHED_IP_PAM scfg ct_IPNR ct_IED ct_IPANX ct_IPCL ct_IPCED ct_MD
        IPCI -> _SCHED_IPCI_PAM scfg ct_IED ct_IPANX ct_IPCL ct_IPCED
        RR   -> _SCHED_RR_PAM scfg ct_IED ct_SD ct_RRANX ct_RRCL ct_RRNXT ct_MD
        RRF  -> _SCHED_RRF_PAM scfg ct_IED ct_RRANX ct_RRCL ct_MD
        SC   -> _SCHED_SC_PAM scfg ct_IED ct_SCEF ct_SCANX ct_SCCL ct_MD
        _    -> Nothing
    LAM -> undefined
