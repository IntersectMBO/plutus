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

module MAlonzo.Code.Type.BetaNBE.Stability where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNBE.Completeness
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Utils

-- Type.BetaNBE.Stability.stability
d_stability_10 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stability_10 = erased
-- Type.BetaNBE.Stability.stabilityNe
d_stabilityNe_14 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 -> AgdaAny
d_stabilityNe_14 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Type.BetaNormal.C_'96'_8 v5
        -> coe
             MAlonzo.Code.Type.BetaNBE.Completeness.du_reflectCR_266 (coe v1)
             erased
      MAlonzo.Code.Type.BetaNormal.C__'183'__10 v4 v6 v7
        -> coe
             MAlonzo.Code.Type.BetaNBE.Completeness.du_transCR_158 (coe v1)
             (coe
                MAlonzo.Code.Type.BetaNBE.d__'183'V__150 (coe v0) (coe v4) (coe v1)
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0)
                   (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v4) (coe v1))
                   (coe MAlonzo.Code.Type.BetaNormal.du_embNe_134 (coe v0) (coe v6))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0) (coe v4)
                   (coe
                      MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                      (coe v7))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
             (coe
                MAlonzo.Code.Type.BetaNBE.d__'183'V__150 (coe v0) (coe v4) (coe v1)
                (coe
                   MAlonzo.Code.Type.BetaNBE.du_reflect_22
                   (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v4) (coe v1)) (coe v6))
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0) (coe v4)
                   (coe
                      MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                      (coe v7))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
             (coe
                MAlonzo.Code.Type.BetaNBE.du_reflect_22 (coe v1)
                (coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v4 v6 v7))
             (coe
                MAlonzo.Code.Type.BetaNBE.Completeness.du_AppCR_376 (coe v0)
                (coe v1)
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0)
                   (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v4) (coe v1))
                   (coe MAlonzo.Code.Type.BetaNormal.du_embNe_134 (coe v0) (coe v6))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                (coe
                   MAlonzo.Code.Type.BetaNBE.du_reflect_22
                   (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v4) (coe v1)) (coe v6))
                (coe
                   d_stabilityNe_14 (coe v0)
                   (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v4) (coe v1)) (coe v6))
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0) (coe v4)
                   (coe
                      MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                      (coe v7))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0) (coe v4)
                   (coe
                      MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                      (coe v7))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
                (coe
                   MAlonzo.Code.Type.BetaNBE.Completeness.d_idext_840 (coe v0)
                   (coe v0) (coe v4) (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)
                   (\ v8 v9 ->
                      coe MAlonzo.Code.Type.BetaNBE.Completeness.du_idCR_1618 v8)
                   (coe
                      MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v4)
                      (coe v7))))
             (coe
                MAlonzo.Code.Type.BetaNBE.Completeness.du_reflectCR_266 (coe v1)
                erased)
      MAlonzo.Code.Type.BetaNormal.C_'94'_12 v5
        -> coe
             MAlonzo.Code.Type.BetaNBE.Completeness.du_reflectCR_266 (coe v1)
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Stability.stability-List
d_stability'45'List_20 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stability'45'List_20 = erased
-- Type.BetaNBE.Stability.stability-VecList
d_stability'45'VecList_28 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stability'45'VecList_28 = erased
