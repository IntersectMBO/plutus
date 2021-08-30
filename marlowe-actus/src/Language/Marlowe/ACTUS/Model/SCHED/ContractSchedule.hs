{-# LANGUAGE RecordWildCards #-}

module Language.Marlowe.ACTUS.Model.SCHED.ContractSchedule where

import           Control.Applicative                                        (Alternative ((<|>)))
import           Data.Maybe                                                 (fromMaybe)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents          (EventType (..))
import           Language.Marlowe.ACTUS.Definitions.ContractState           (ContractStatePoly (tmd))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms           (CT (..), ContractTerms (..))
import           Language.Marlowe.ACTUS.Definitions.Schedule                (ShiftedDay (calculationDay))
import           Language.Marlowe.ACTUS.Model.INIT.StateInitializationModel (_INIT_LAM, _INIT_NAM)
import           Language.Marlowe.ACTUS.Model.SCHED.ContractScheduleModel
import           Language.Marlowe.ACTUS.Model.Utility.ANN.Maturity          (maturity)
import           Language.Marlowe.ACTUS.Model.Utility.ScheduleGenerator     (inf, sup)

schedule :: EventType -> ContractTerms -> Maybe [ShiftedDay]
schedule ev ct@ContractTerms{..} =
  case contractType of
    PAM -> case ev of
        IED  -> _SCHED_IED_PAM ct
        MD   -> _SCHED_MD_PAM ct
        PP   -> _SCHED_PP_PAM ct
        PY   -> _SCHED_PY_PAM ct
        FP   -> _SCHED_FP_PAM ct
        PRD  -> _SCHED_PRD_PAM ct
        TD   -> _SCHED_TD_PAM ct
        IP   -> _SCHED_IP_PAM ct
        IPCI -> _SCHED_IPCI_PAM ct
        RR   -> _SCHED_RR_PAM ct
        RRF  -> _SCHED_RRF_PAM ct
        SC   -> _SCHED_SC_PAM ct
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
        _tmd = Just $ tmd $ _INIT_LAM ct_SD tminus tpr_minus tfp_minus tfp_plus ct
      in case ev of
        IED  -> _SCHED_IED_PAM ct
        PR   -> _SCHED_PR_LAM ct { ct_MD = _tmd }
        MD   -> _SCHED_MD_LAM ct { ct_MD = _tmd }
        PP   -> _SCHED_PP_PAM ct { ct_MD = _tmd }
        PY   -> _SCHED_PY_PAM ct { ct_MD = _tmd }
        FP   -> _SCHED_FP_PAM ct { ct_MD = _tmd }
        PRD  -> _SCHED_PRD_PAM ct
        TD   -> _SCHED_TD_PAM ct
        IP   -> _SCHED_IP_PAM ct { ct_MD = _tmd }
        IPCI -> _SCHED_IPCI_PAM ct { ct_MD = _tmd }
        IPCB -> _SCHED_IPCB_LAM ct { ct_MD = _tmd }
        RR   -> _SCHED_RR_PAM ct { ct_MD = _tmd }
        RRF  -> _SCHED_RRF_PAM ct { ct_MD = _tmd }
        SC   -> _SCHED_SC_PAM ct { ct_MD = _tmd }
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
        _tmd = Just $ tmd $ _INIT_NAM ct_SD tminus tpr_minus tfp_minus tfp_plus ct
      in case ev of
        IED  -> _SCHED_IED_PAM ct
        PR   -> _SCHED_PR_LAM ct { ct_MD = _tmd }
        MD   -> _SCHED_MD_PAM ct { ct_MD = _tmd }
        PP   -> _SCHED_PP_PAM ct { ct_MD = _tmd }
        PY   -> _SCHED_PY_PAM ct { ct_MD = _tmd }
        FP   -> _SCHED_FP_PAM ct { ct_MD = _tmd }
        PRD  -> _SCHED_PRD_PAM ct
        TD   -> _SCHED_TD_PAM ct
        IP   -> _SCHED_IP_NAM ct { ct_MD = _tmd }
        IPCI -> _SCHED_IPCI_NAM ct { ct_MD = _tmd }
        IPCB -> _SCHED_IPCB_LAM ct { ct_MD = _tmd }
        RR   -> _SCHED_RR_PAM ct { ct_MD = _tmd }
        RRF  -> _SCHED_RRF_PAM ct { ct_MD = _tmd }
        SC   -> _SCHED_SC_PAM ct { ct_MD = _tmd }
        _    -> Nothing

    ANN ->
      let mat = maturity ct
          _tmd = ct_AD <|> mat
      in case ev of
        IED  -> _SCHED_IED_PAM ct
        PR   -> _SCHED_PR_LAM ct { ct_MD = _tmd }
        MD   -> _SCHED_MD_PAM ct { ct_MD = ct_MD <|> _tmd }
        PP   -> _SCHED_PP_PAM ct { ct_MD = _tmd }
        PY   -> _SCHED_PY_PAM ct { ct_MD = _tmd }
        FP   -> _SCHED_FP_PAM ct { ct_MD = _tmd }
        PRD  -> _SCHED_PRD_PAM ct { ct_MD = _tmd }
        TD   -> _SCHED_TD_PAM ct { ct_MD = _tmd }
        IP   -> _SCHED_IP_NAM ct { ct_MD = ct_MD <|> _tmd }
        IPCI -> _SCHED_IPCI_PAM ct { ct_MD = _tmd }
        IPCB -> _SCHED_IPCB_LAM ct { ct_MD = _tmd }
        RR   -> _SCHED_RR_PAM ct { ct_MD = _tmd }
        RRF  -> _SCHED_RRF_PAM ct { ct_MD = _tmd }
        SC   -> _SCHED_SC_PAM ct { ct_MD = _tmd }
        PRF  -> let prf = _SCHED_PRF_ANN ct { ct_MD = _tmd }
                    rr  = _SCHED_RR_PAM ct { ct_MD = _tmd }
                    rrf = _SCHED_RRF_PAM ct { ct_MD = _tmd }
                in Just $ fromMaybe [] prf ++ fromMaybe [] rr ++ fromMaybe [] rrf
        _    -> Nothing
