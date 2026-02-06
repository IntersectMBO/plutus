{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Algorithmic.Evaluation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Algorithmic.ReductionEC
import qualified MAlonzo.Code.Algorithmic.ReductionEC.Progress
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Utils

-- Algorithmic.Evaluation.Gas
d_Gas_4 = ()
newtype T_Gas_4 = C_gas_6 Integer
-- Algorithmic.Evaluation.Finished
d_Finished_12 a0 a1 = ()
data T_Finished_12
  = C_done_18 MAlonzo.Code.Algorithmic.ReductionEC.T_Value_28 |
    C_out'45'of'45'gas_22 |
    C_error_26 MAlonzo.Code.Algorithmic.ReductionEC.T_Error_338
-- Algorithmic.Evaluation.Steps
d_Steps_30 a0 a1 = ()
data T_Steps_30
  = C_steps_38 MAlonzo.Code.Algorithmic.T__'8866'__178
               MAlonzo.Code.Algorithmic.ReductionEC.T__'8212''8608'__780
               T_Finished_12
-- Algorithmic.Evaluation.eval—→
d_eval'8212''8594'_46 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.ReductionEC.T__'8212''8594'__750 ->
  T_Steps_30 -> T_Steps_30
d_eval'8212''8594'_46 ~v0 ~v1 v2 v3 v4
  = du_eval'8212''8594'_46 v2 v3 v4
du_eval'8212''8594'_46 ::
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.ReductionEC.T__'8212''8594'__750 ->
  T_Steps_30 -> T_Steps_30
du_eval'8212''8594'_46 v0 v1 v2
  = case coe v2 of
      C_steps_38 v5 v6 v7
        -> coe
             C_steps_38 v5
             (coe
                MAlonzo.Code.Algorithmic.ReductionEC.C_trans'8212''8608'_796 v0 v1
                v6)
             v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Evaluation.eval
d_eval_58 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_Gas_4 -> MAlonzo.Code.Algorithmic.T__'8866'__178 -> T_Steps_30
d_eval_58 v0 v1 v2
  = case coe v1 of
      C_gas_6 v3
        -> case coe v3 of
             0 -> coe
                    C_steps_38 v2
                    (coe MAlonzo.Code.Algorithmic.ReductionEC.C_refl'8212''8608'_786)
                    (coe C_out'45'of'45'gas_22)
             _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d_evalProg_64 (coe v0) (coe C_gas_6 (coe v4)) (coe v2)
                       (coe
                          MAlonzo.Code.Algorithmic.ReductionEC.Progress.d_progress_86
                          (coe v0) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Evaluation.evalProg
d_evalProg_64 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  T_Gas_4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Algorithmic.ReductionEC.Progress.T_Progress_10 ->
  T_Steps_30
d_evalProg_64 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Algorithmic.ReductionEC.Progress.C_step_18 v4 v5
        -> let v6
                 = coe
                     du_eval'8212''8594'_46 (coe v4) (coe v5)
                     (coe d_eval_58 (coe v0) (coe v1) (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Algorithmic.ReductionEC.C_ruleErr_776 v7 v9
                  -> case coe v9 of
                       MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480
                         -> coe
                              C_steps_38
                              (coe
                                 MAlonzo.Code.Algorithmic.ReductionEC.du__'91'_'93''7473'_574
                                 (coe v0) (coe MAlonzo.Code.Algorithmic.ReductionEC.C_'91''93'_480)
                                 (coe MAlonzo.Code.Algorithmic.C_error_268))
                              (coe MAlonzo.Code.Algorithmic.ReductionEC.C_refl'8212''8608'_786)
                              (coe
                                 C_error_26
                                 (coe MAlonzo.Code.Algorithmic.ReductionEC.C_E'45'error_346))
                       _ -> coe v6
                _ -> coe v6)
      MAlonzo.Code.Algorithmic.ReductionEC.Progress.C_done_20 v4
        -> coe
             C_steps_38 v2
             (coe MAlonzo.Code.Algorithmic.ReductionEC.C_refl'8212''8608'_786)
             (coe C_done_18 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Evaluation.stepper
d_stepper_86 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Utils.T_RuntimeError_396
    MAlonzo.Code.Algorithmic.T__'8866'__178
d_stepper_86 v0 v1 v2
  = let v3 = d_eval_58 (coe v0) (coe C_gas_6 (coe v2)) (coe v1) in
    coe
      (case coe v3 of
         C_steps_38 v6 v7 v8
           -> case coe v8 of
                C_done_18 v10 -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v6)
                C_out'45'of'45'gas_22
                  -> coe
                       MAlonzo.Code.Utils.C_inj'8321'_12
                       (coe MAlonzo.Code.Utils.C_gasError_398)
                C_error_26 v10
                  -> coe
                       MAlonzo.Code.Utils.C_inj'8322'_14
                       (coe MAlonzo.Code.Algorithmic.C_error_268)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
