{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule where

import           Control.Applicative                                        (Alternative ((<|>)))
import           Data.Maybe                                                 (fromJust, fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractStatePoly (tmd))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_LAM, _INIT_NAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Maturity          (maturity)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (inf, sup)

schedule :: EventType -> ContractTerms -> Maybe [ShiftedDay]
schedule ev
  ct@ContractTerms {
      ct_IED  = ct_IED
    , ct_FER  = ct_FER
    , ct_MD   = ct_MD
    , ct_PRD  = ct_PRD
    , ct_TD   = ct_TD
    , ct_SCEF = ct_SCEF
    , ct_PYTP = ct_PYTP
    , ct_PPEF = ct_PPEF
    , ..} =
    let
        ct_IED'  = fromJust ct_IED
        ct_FER'  = fromJust ct_FER
        ct_MD'   = fromJust ct_MD
        ct_SCEF' = fromJust ct_SCEF
        ct_PYTP' = fromJust ct_PYTP
        ct_PPEF' = fromJust ct_PPEF
    in
      case contractType of
        PAM -> case ev of
            IED  -> _SCHED_IED_PAM scfg ct_IED'
            MD   -> _SCHED_MD_PAM scfg ct_MD'
            PP   -> _SCHED_PP_PAM scfg ct_PPEF' ct_OPCL ct_IED' ct_OPANX ct_MD'
            PY   -> _SCHED_PY_PAM scfg ct_PYTP' ct_PPEF' ct_OPCL ct_IED' ct_OPANX ct_MD'
            FP   -> _SCHED_FP_PAM scfg ct_FER' ct_FECL ct_IED' ct_FEANX ct_MD'
            PRD  -> _SCHED_PRD_PAM scfg ct_PRD
            TD   -> _SCHED_TD_PAM scfg ct_TD
            IP   -> _SCHED_IP_PAM scfg ct_IPNR ct_IED' ct_IPANX ct_IPCL ct_IPCED ct_MD'
            IPCI -> _SCHED_IPCI_PAM scfg ct_IED' ct_IPANX ct_IPCL ct_IPCED ct_MD' ct_IPNR
            RR   -> _SCHED_RR_PAM scfg ct_IED' ct_SD ct_RRANX ct_RRCL ct_RRNXT ct_MD'
            RRF  -> _SCHED_RRF_PAM scfg ct_IED' ct_RRANX ct_RRCL ct_RRNXT ct_MD' ct_SD
            SC   -> _SCHED_SC_PAM scfg ct_IED' ct_SCEF' ct_SCANX ct_SCCL ct_MD'
            _    -> Nothing
        LAM ->
          let
            -- Need LAM state initialization since MD schedule is Tmd0 which may consist of other terms
            -- Also cannot call initializeState directly without cyclical imports
            t0                 = ct_SD
            fpSchedule         = schedule FP ct
            tfp_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< fpSchedule)
            tfp_plus           = maybe t0 calculationDay ((\sc -> inf sc t0) =<< fpSchedule)
            ipSchedule         = schedule IP ct
            tminus             = maybe t0 calculationDay ((\sc -> sup sc t0) =<< ipSchedule)
            prSchedule         = schedule PR ct
            tpr_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< prSchedule)
            _tmd = tmd $ _INIT_LAM ct_SD tminus tpr_minus tfp_minus tfp_plus ct
          in case ev of
            IED  -> _SCHED_IED_PAM scfg ct_IED'
            PR   -> _SCHED_PR_LAM scfg ct_PRCL ct_IED' ct_PRANX _tmd
            MD   -> _SCHED_MD_LAM scfg _tmd
            PP   -> _SCHED_PP_PAM scfg ct_PPEF' ct_OPCL ct_IED' ct_OPANX _tmd
            PY   -> _SCHED_PY_PAM scfg ct_PYTP' ct_PPEF' ct_OPCL ct_IED' ct_OPANX _tmd
            FP   -> _SCHED_FP_PAM scfg ct_FER' ct_FECL ct_IED' ct_FEANX _tmd
            PRD  -> _SCHED_PRD_PAM scfg ct_PRD
            TD   -> _SCHED_TD_PAM scfg ct_TD
            IP   -> _SCHED_IP_PAM scfg ct_IPNR ct_IED' ct_IPANX ct_IPCL ct_IPCED _tmd
            IPCI -> _SCHED_IPCI_PAM scfg ct_IED' ct_IPANX ct_IPCL ct_IPCED _tmd ct_IPNR
            IPCB -> _SCHED_IPCB_LAM scfg ct_IED' ct_IPCB ct_IPCBCL ct_IPCBANX _tmd
            RR   -> _SCHED_RR_PAM scfg ct_IED' ct_SD ct_RRANX ct_RRCL ct_RRNXT _tmd
            RRF  -> _SCHED_RRF_PAM scfg ct_IED' ct_RRANX ct_RRCL ct_RRNXT _tmd ct_SD
            SC   -> _SCHED_SC_PAM scfg ct_IED' ct_SCEF' ct_SCANX ct_SCCL _tmd
            _    -> Nothing
        NAM ->
          -- Same as LAM - need to calculate Tmd0
          -- TODO: refactor for LAM and NAM
          let
            t0                 = ct_SD
            fpSchedule         = schedule FP ct
            tfp_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< fpSchedule)
            tfp_plus           = maybe t0 calculationDay ((\sc -> inf sc t0) =<< fpSchedule)
            ipSchedule         = schedule IP ct
            tminus             = maybe t0 calculationDay ((\sc -> sup sc t0) =<< ipSchedule)
            prSchedule         = schedule PR ct
            tpr_minus          = maybe t0 calculationDay ((\sc -> sup sc t0) =<< prSchedule)
            _tmd = tmd $ _INIT_NAM ct_SD tminus tpr_minus tfp_minus tfp_plus ct
          in case ev of
            IED  -> _SCHED_IED_PAM scfg ct_IED'
            PR   -> _SCHED_PR_LAM scfg ct_PRCL ct_IED' ct_PRANX _tmd
            MD   -> _SCHED_MD_PAM scfg _tmd
            PP   -> _SCHED_PP_PAM scfg ct_PPEF' ct_OPCL ct_IED' ct_OPANX _tmd
            PY   -> _SCHED_PY_PAM scfg ct_PYTP' ct_PPEF' ct_OPCL ct_IED' ct_OPANX _tmd
            FP   -> _SCHED_FP_PAM scfg ct_FER' ct_FECL ct_IED' ct_FEANX _tmd
            PRD  -> _SCHED_PRD_PAM scfg ct_PRD
            TD   -> _SCHED_TD_PAM scfg ct_TD
            IP   -> _SCHED_IP_NAM scfg ct_IED' ct_PRCL ct_PRANX ct_IPCED ct_IPANX ct_IPCL _tmd
            IPCI -> _SCHED_IPCI_NAM scfg ct_IED' ct_PRCL ct_PRANX ct_IPCED ct_IPANX ct_IPCL _tmd
            IPCB -> _SCHED_IPCB_LAM scfg ct_IED' ct_IPCB ct_IPCBCL ct_IPCBANX _tmd
            RR   -> _SCHED_RR_PAM scfg ct_IED' ct_SD ct_RRANX ct_RRCL ct_RRNXT _tmd
            RRF  -> _SCHED_RRF_PAM scfg ct_IED' ct_RRANX ct_RRCL ct_RRNXT _tmd ct_SD
            SC   -> _SCHED_SC_PAM scfg ct_IED' ct_SCEF' ct_SCANX ct_SCCL _tmd
            _    -> Nothing

        ANN ->
          let mat = maturity ct
              _tmd = ct_AD <|> mat

          in case ev of
            IED  -> _SCHED_IED_PAM scfg ct_IED'
            PR   -> _tmd >>= _SCHED_PR_LAM scfg ct_PRCL ct_IED' ct_PRANX
            MD   -> ct_MD <|> _tmd >>= _SCHED_MD_PAM scfg
            PP   -> _tmd >>= _SCHED_PP_PAM scfg ct_PPEF' ct_OPCL ct_IED' ct_OPANX
            PY   -> _tmd >>= _SCHED_PY_PAM scfg ct_PYTP' ct_PPEF' ct_OPCL ct_IED' ct_OPANX
            FP   -> _tmd >>= _SCHED_FP_PAM scfg ct_FER' ct_FECL ct_IED' ct_FEANX
            PRD  -> _SCHED_PRD_PAM scfg ct_PRD
            TD   -> _SCHED_TD_PAM scfg ct_TD
            IP   -> ct_MD <|> _tmd >>= _SCHED_IP_NAM scfg ct_IED' ct_PRCL ct_PRANX ct_IPCED ct_IPANX ct_IPCL
            IPCI -> _tmd >>= \t -> _SCHED_IPCI_PAM scfg ct_IED' ct_IPANX ct_IPCL ct_IPCED t ct_IPNR
            IPCB -> _tmd >>= _SCHED_IPCB_LAM scfg ct_IED' ct_IPCB ct_IPCBCL ct_IPCBANX
            RR   -> _tmd >>= _SCHED_RR_PAM scfg ct_IED' ct_SD ct_RRANX ct_RRCL ct_RRNXT
            RRF  -> _tmd >>= \t -> _SCHED_RRF_PAM scfg ct_IED' ct_RRANX ct_RRCL ct_RRNXT t ct_SD
            SC   -> _tmd >>= _SCHED_SC_PAM scfg ct_IED' ct_SCEF' ct_SCANX ct_SCCL
            PRF  -> let prf = _SCHED_PRF_ANN ct_PRANX ct_PRNXT ct_IED
                        rr  = _tmd >>= _SCHED_RR_PAM scfg ct_IED' ct_SD ct_RRANX ct_RRCL ct_RRNXT
                        rrf = _tmd >>= \t -> _SCHED_RRF_PAM scfg ct_IED' ct_RRANX ct_RRCL ct_RRNXT t ct_SD
                    in Just $ fromMaybe [] prf ++ fromMaybe [] rr ++ fromMaybe [] rrf
            _    -> Nothing
