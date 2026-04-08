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

module MAlonzo.Code.Induction.WellFounded where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Induction

-- Induction.WellFounded.WfRec
d_WfRec_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d_WfRec_22 = erased
-- Induction.WellFounded.Acc
d_Acc_42 a0 a1 a2 a3 a4 = ()
data T_Acc_42 = C_acc_52
-- Induction.WellFounded.WellFounded
d_WellFounded_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> ()
d_WellFounded_54 = erased
-- Induction.WellFounded.acc-inverse
d_acc'45'inverse_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> T_Acc_42 -> AgdaAny -> AgdaAny -> T_Acc_42
d_acc'45'inverse_66 = erased
-- Induction.WellFounded._.Acc-resp-flip-≈
d_Acc'45'resp'45'flip'45''8776'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_Acc_42 -> T_Acc_42
d_Acc'45'resp'45'flip'45''8776'_86 = erased
-- Induction.WellFounded._.Acc-resp-≈
d_Acc'45'resp'45''8776'_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_Acc_42 -> T_Acc_42
d_Acc'45'resp'45''8776'_96 = erased
-- Induction.WellFounded.Some.wfRecBuilder
d_wfRecBuilder_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> T_Acc_42 -> AgdaAny -> AgdaAny -> AgdaAny
d_wfRecBuilder_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 ~v10
  = du_wfRecBuilder_116 v6 v9
du_wfRecBuilder_116 ::
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_wfRecBuilder_116 v0 v1
  = coe v0 v1 (\ v2 v3 -> coe du_wfRecBuilder_116 (coe v0) v2)
-- Induction.WellFounded.Some.wfRec
d_wfRec_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> T_Acc_42 -> AgdaAny
d_wfRec_128 ~v0 ~v1 ~v2 ~v3 ~v4 = du_wfRec_128
du_wfRec_128 ::
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> T_Acc_42 -> AgdaAny
du_wfRec_128
  = coe
      MAlonzo.Code.Induction.du_subsetBuild_62
      (\ v0 v1 v2 v3 v4 v5 -> coe du_wfRecBuilder_116 v1 v4)
-- Induction.WellFounded.Some.unfold-wfRec
d_unfold'45'wfRec_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny ->
  T_Acc_42 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45'wfRec_140 = erased
-- Induction.WellFounded.All.wfRecBuilder
d_wfRecBuilder_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_wfRecBuilder_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9
  = du_wfRecBuilder_160 v7 v9
du_wfRecBuilder_160 ::
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_wfRecBuilder_160 v0 v1 v2
  = coe du_wfRecBuilder_116 (coe v0) (coe v1)
-- Induction.WellFounded.All.wfRec
d_wfRec_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny
d_wfRec_168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_wfRec_168
du_wfRec_168 ::
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_wfRec_168
  = coe
      MAlonzo.Code.Induction.du_build_36
      (\ v0 v1 v2 v3 -> coe du_wfRecBuilder_160 v1 v3)
-- Induction.WellFounded.All.wfRec-builder
d_wfRec'45'builder_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_wfRec'45'builder_170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_wfRec'45'builder_170
du_wfRec'45'builder_170 ::
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_wfRec'45'builder_170 v0 v1 v2 v3 = coe du_wfRecBuilder_160 v1 v3
-- Induction.WellFounded.FixPoint.some-wfrec-Irrelevant
d_some'45'wfrec'45'Irrelevant_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> ()
d_some'45'wfrec'45'Irrelevant_200 = erased
-- Induction.WellFounded.FixPoint.some-wfRec-irrelevant
d_some'45'wfRec'45'irrelevant_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  T_Acc_42 ->
  T_Acc_42 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_some'45'wfRec'45'irrelevant_210 = erased
-- Induction.WellFounded.FixPoint._.wfRec
d_wfRec_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny
d_wfRec_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_wfRec_226
du_wfRec_226 ::
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_wfRec_226 = coe du_wfRec_168
-- Induction.WellFounded.FixPoint._.wfRec-builder
d_wfRec'45'builder_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_wfRec'45'builder_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_wfRec'45'builder_228
du_wfRec'45'builder_228 ::
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_wfRec'45'builder_228 = coe du_wfRec'45'builder_170
-- Induction.WellFounded.FixPoint._.wfRecBuilder
d_wfRecBuilder_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_wfRecBuilder_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_wfRecBuilder_230
du_wfRecBuilder_230 ::
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_wfRecBuilder_230 v0 v1 v2 v3 = coe du_wfRecBuilder_160 v1 v3
-- Induction.WellFounded.FixPoint.wfRecBuilder-wfRec
d_wfRecBuilder'45'wfRec_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wfRecBuilder'45'wfRec_238 = erased
-- Induction.WellFounded.FixPoint.unfold-wfRec
d_unfold'45'wfRec_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   (AgdaAny ->
    AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45'wfRec_256 = erased
-- Induction.WellFounded._.acc⇒asym
d_acc'8658'asym_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  T_Acc_42 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_acc'8658'asym_274 = erased
-- Induction.WellFounded._.wf⇒asym
d_wf'8658'asym_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_wf'8658'asym_292 = erased
-- Induction.WellFounded._.wf⇒irrefl
d_wf'8658'irrefl_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> T_Acc_42) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_wf'8658'irrefl_298 = erased
-- Induction.WellFounded.Subrelation.accessible
d_accessible_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Acc_42 -> T_Acc_42
d_accessible_324 = erased
-- Induction.WellFounded.Subrelation.wellFounded
d_wellFounded_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> T_Acc_42) -> AgdaAny -> T_Acc_42
d_wellFounded_330 = erased
-- Induction.WellFounded.InverseImage.accessible
d_accessible_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_Acc_42 -> T_Acc_42
d_accessible_350 = erased
-- Induction.WellFounded.InverseImage.wellFounded
d_wellFounded_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> T_Acc_42) -> AgdaAny -> T_Acc_42
d_wellFounded_356 = erased
-- Induction.WellFounded.InverseImage.well-founded
d_well'45'founded_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> T_Acc_42) -> AgdaAny -> T_Acc_42
d_well'45'founded_362 = erased
-- Induction.WellFounded.TransitiveClosure._<⁺_
d__'60''8314'__374 a0 a1 a2 a3 a4 a5 = ()
data T__'60''8314'__374
  = C_'91'_'93'_382 AgdaAny |
    C_trans_394 AgdaAny T__'60''8314'__374 T__'60''8314'__374
-- Induction.WellFounded.TransitiveClosure.downwardsClosed
d_downwardsClosed_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Acc_42 -> T__'60''8314'__374 -> T_Acc_42
d_downwardsClosed_400 = erased
-- Induction.WellFounded.TransitiveClosure.accessible
d_accessible_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> T_Acc_42 -> T_Acc_42
d_accessible_410 = erased
-- Induction.WellFounded.TransitiveClosure.accessible′
d_accessible'8242'_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> T_Acc_42 -> AgdaAny -> T__'60''8314'__374 -> T_Acc_42
d_accessible'8242'_414 = erased
-- Induction.WellFounded.TransitiveClosure.wellFounded
d_wellFounded_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) -> AgdaAny -> T_Acc_42
d_wellFounded_428 = erased
-- Induction.WellFounded.Lexicographic._<_
d__'60'__454 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T__'60'__454 = C_left_466 AgdaAny | C_right_476 AgdaAny
-- Induction.WellFounded.Lexicographic.accessible
d_accessible_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> T_Acc_42 -> (AgdaAny -> AgdaAny -> T_Acc_42) -> T_Acc_42
d_accessible_484 = erased
-- Induction.WellFounded.Lexicographic.accessible′
d_accessible'8242'_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  T_Acc_42 ->
  T_Acc_42 ->
  (AgdaAny -> AgdaAny -> T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T__'60'__454 -> T_Acc_42
d_accessible'8242'_492 = erased
-- Induction.WellFounded.Lexicographic.wellFounded
d_wellFounded_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> AgdaAny -> T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Acc_42
d_wellFounded_514 = erased
-- Induction.WellFounded.Lexicographic.well-founded
d_well'45'founded_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) ->
  (AgdaAny -> AgdaAny -> T_Acc_42) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Acc_42
d_well'45'founded_522 = erased
-- Induction.WellFounded.Inverse-image.accessible
d_accessible_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_Acc_42 -> T_Acc_42
d_accessible_526 = erased
-- Induction.WellFounded.Inverse-image.well-founded
d_well'45'founded_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> T_Acc_42) -> AgdaAny -> T_Acc_42
d_well'45'founded_528 = erased
-- Induction.WellFounded.Inverse-image.wellFounded
d_wellFounded_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> T_Acc_42) -> AgdaAny -> T_Acc_42
d_wellFounded_530 = erased
-- Induction.WellFounded.Transitive-closure._<⁺_
d__'60''8314'__534 a0 a1 a2 a3 a4 a5 = ()
-- Induction.WellFounded.Transitive-closure.accessible
d_accessible_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> T_Acc_42 -> T_Acc_42
d_accessible_538 = erased
-- Induction.WellFounded.Transitive-closure.accessible′
d_accessible'8242'_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> T_Acc_42 -> AgdaAny -> T__'60''8314'__374 -> T_Acc_42
d_accessible'8242'_540 = erased
-- Induction.WellFounded.Transitive-closure.downwardsClosed
d_downwardsClosed_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Acc_42 -> T__'60''8314'__374 -> T_Acc_42
d_downwardsClosed_542 = erased
-- Induction.WellFounded.Transitive-closure.wellFounded
d_wellFounded_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> T_Acc_42) -> AgdaAny -> T_Acc_42
d_wellFounded_546 = erased
-- Induction.WellFounded..generalizedField-A.a
d_'46'generalizedField'45'A'46'a_6265 ::
  T_GeneralizeTel_6271 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'A'46'a_6265 v0
  = case coe v0 of
      C_mkGeneralizeTel_6273 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Induction.WellFounded..generalizedField-A
d_'46'generalizedField'45'A_6267 :: T_GeneralizeTel_6271 -> ()
d_'46'generalizedField'45'A_6267 = erased
-- Induction.WellFounded..generalizedField-r
d_'46'generalizedField'45'r_6269 ::
  T_GeneralizeTel_6271 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'r_6269 v0
  = case coe v0 of
      C_mkGeneralizeTel_6273 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Induction.WellFounded.GeneralizeTel
d_GeneralizeTel_6271 = ()
data T_GeneralizeTel_6271
  = C_mkGeneralizeTel_6273 MAlonzo.Code.Agda.Primitive.T_Level_18
                           MAlonzo.Code.Agda.Primitive.T_Level_18
-- Induction.WellFounded..generalizedField-A.a
d_'46'generalizedField'45'A'46'a_10331 ::
  T_GeneralizeTel_10337 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'A'46'a_10331 v0
  = case coe v0 of
      C_mkGeneralizeTel_10339 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Induction.WellFounded..generalizedField-A
d_'46'generalizedField'45'A_10333 :: T_GeneralizeTel_10337 -> ()
d_'46'generalizedField'45'A_10333 = erased
-- Induction.WellFounded..generalizedField-r
d_'46'generalizedField'45'r_10335 ::
  T_GeneralizeTel_10337 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'r_10335 v0
  = case coe v0 of
      C_mkGeneralizeTel_10339 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Induction.WellFounded.GeneralizeTel
d_GeneralizeTel_10337 = ()
data T_GeneralizeTel_10337
  = C_mkGeneralizeTel_10339 MAlonzo.Code.Agda.Primitive.T_Level_18
                            MAlonzo.Code.Agda.Primitive.T_Level_18
