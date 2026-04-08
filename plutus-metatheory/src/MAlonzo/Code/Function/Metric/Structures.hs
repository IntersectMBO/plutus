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

module MAlonzo.Code.Function.Metric.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Function.Metric.Structures.IsProtoMetric
d_IsProtoMetric_30 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_IsProtoMetric_30
  = C_constructor_100 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
                      MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
                      (AgdaAny ->
                       AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsProtoMetric.isPartialOrder
d_isPartialOrder_42 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_42 v0
  = case coe v0 of
      C_constructor_100 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsProtoMetric.≈-isEquivalence
d_'8776''45'isEquivalence_44 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_44 v0
  = case coe v0 of
      C_constructor_100 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsProtoMetric.cong
d_cong_46 ::
  T_IsProtoMetric_30 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_46 v0
  = case coe v0 of
      C_constructor_100 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsProtoMetric.nonNegative
d_nonNegative_48 ::
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_48 v0
  = case coe v0 of
      C_constructor_100 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsProtoMetric._.antisym
d_antisym_52 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_52 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_42 (coe v0))
-- Function.Metric.Structures.IsProtoMetric._.isEquivalence
d_isEquivalence_54 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_54 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_42 (coe v0)))
-- Function.Metric.Structures.IsProtoMetric._.isPreorder
d_isPreorder_56 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_56 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_42 (coe v0))
-- Function.Metric.Structures.IsProtoMetric._.refl
d_refl_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny
d_refl_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_refl_58 v12
du_refl_58 :: T_IsProtoMetric_30 -> AgdaAny -> AgdaAny
du_refl_58 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Function.Metric.Structures.IsProtoMetric._.reflexive
d_reflexive_60 ::
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_60 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_42 (coe v0)))
-- Function.Metric.Structures.IsProtoMetric._.trans
d_trans_62 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_62 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_42 (coe v0)))
-- Function.Metric.Structures.IsProtoMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'45''8776'_64 v12
du_'8764''45'resp'45''8776'_64 ::
  T_IsProtoMetric_30 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_64 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Function.Metric.Structures.IsProtoMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'691''45''8776'_66 v12
du_'8764''45'resp'691''45''8776'_66 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_66 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Function.Metric.Structures.IsProtoMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_68 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'737''45''8776'_68 v12
du_'8764''45'resp'737''45''8776'_68 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_68 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Function.Metric.Structures.IsProtoMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'45''8776'_70 v12
du_'8818''45'resp'45''8776'_70 ::
  T_IsProtoMetric_30 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_70 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Function.Metric.Structures.IsProtoMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'691''45''8776'_72 v12
du_'8818''45'resp'691''45''8776'_72 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_72 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Function.Metric.Structures.IsProtoMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'737''45''8776'_74 v12
du_'8818''45'resp'737''45''8776'_74 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_74 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Function.Metric.Structures.IsProtoMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12
  = du_isPartialEquivalence_78 v12
du_isPartialEquivalence_78 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_78 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
               (coe v2))))
-- Function.Metric.Structures.IsProtoMetric._.Eq.refl
d_refl_80 :: T_IsProtoMetric_30 -> AgdaAny -> AgdaAny
d_refl_80 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_42 (coe v0))))
-- Function.Metric.Structures.IsProtoMetric._.Eq.reflexive
d_reflexive_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               v12
  = du_reflexive_82 v12
du_reflexive_82 ::
  T_IsProtoMetric_30 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_82 v0
  = let v1 = d_isPartialOrder_42 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                 (coe v2))
              v3))
-- Function.Metric.Structures.IsProtoMetric._.Eq.sym
d_sym_84 ::
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_84 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_42 (coe v0))))
-- Function.Metric.Structures.IsProtoMetric._.Eq.trans
d_trans_86 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_86 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_42 (coe v0))))
-- Function.Metric.Structures.IsProtoMetric.EqC.isPartialEquivalence
d_isPartialEquivalence_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12
  = du_isPartialEquivalence_90 v12
du_isPartialEquivalence_90 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_90 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe d_'8776''45'isEquivalence_44 (coe v0))
-- Function.Metric.Structures.IsProtoMetric.EqC.refl
d_refl_92 :: T_IsProtoMetric_30 -> AgdaAny -> AgdaAny
d_refl_92 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_'8776''45'isEquivalence_44 (coe v0))
-- Function.Metric.Structures.IsProtoMetric.EqC.reflexive
d_reflexive_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsProtoMetric_30 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               v12
  = du_reflexive_94 v12
du_reflexive_94 ::
  T_IsProtoMetric_30 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
      (coe d_'8776''45'isEquivalence_44 (coe v0)) v1
-- Function.Metric.Structures.IsProtoMetric.EqC.sym
d_sym_96 ::
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_96 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_'8776''45'isEquivalence_44 (coe v0))
-- Function.Metric.Structures.IsProtoMetric.EqC.trans
d_trans_98 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_98 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_'8776''45'isEquivalence_44 (coe v0))
-- Function.Metric.Structures.IsPreMetric
d_IsPreMetric_104 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_IsPreMetric_104
  = C_constructor_174 T_IsProtoMetric_30
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsPreMetric.isProtoMetric
d_isProtoMetric_112 :: T_IsPreMetric_104 -> T_IsProtoMetric_30
d_isProtoMetric_112 v0
  = case coe v0 of
      C_constructor_174 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsPreMetric.≈⇒0
d_'8776''8658'0_114 ::
  T_IsPreMetric_104 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_114 v0
  = case coe v0 of
      C_constructor_174 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsPreMetric._.antisym
d_antisym_118 ::
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_118 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.cong
d_cong_120 ::
  T_IsPreMetric_104 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_120 v0 = coe d_cong_46 (coe d_isProtoMetric_112 (coe v0))
-- Function.Metric.Structures.IsPreMetric._.isEquivalence
d_isEquivalence_122 ::
  T_IsPreMetric_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_122 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0))))
-- Function.Metric.Structures.IsPreMetric._.isPartialOrder
d_isPartialOrder_124 ::
  T_IsPreMetric_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_124 v0
  = coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0))
-- Function.Metric.Structures.IsPreMetric._.isPreorder
d_isPreorder_126 ::
  T_IsPreMetric_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_126 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.nonNegative
d_nonNegative_128 ::
  T_IsPreMetric_104 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_128 v0
  = coe d_nonNegative_48 (coe d_isProtoMetric_112 (coe v0))
-- Function.Metric.Structures.IsPreMetric._.refl
d_refl_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 -> AgdaAny -> AgdaAny
d_refl_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_refl_130 v12
du_refl_130 :: T_IsPreMetric_104 -> AgdaAny -> AgdaAny
du_refl_130 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.reflexive
d_reflexive_132 ::
  T_IsPreMetric_104 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_132 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0))))
-- Function.Metric.Structures.IsPreMetric._.trans
d_trans_134 ::
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_134 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0))))
-- Function.Metric.Structures.IsPreMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_136 ::
  T_IsPreMetric_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_136 v0
  = coe
      d_'8776''45'isEquivalence_44 (coe d_isProtoMetric_112 (coe v0))
-- Function.Metric.Structures.IsPreMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'45''8776'_138 v12
du_'8764''45'resp'45''8776'_138 ::
  T_IsPreMetric_104 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_138 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'691''45''8776'_140 v12
du_'8764''45'resp'691''45''8776'_140 ::
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_140 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'737''45''8776'_142 v12
du_'8764''45'resp'737''45''8776'_142 ::
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_142 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'45''8776'_144 v12
du_'8818''45'resp'45''8776'_144 ::
  T_IsPreMetric_104 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_144 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'691''45''8776'_146 v12
du_'8818''45'resp'691''45''8776'_146 ::
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_146 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'737''45''8776'_148 v12
du_'8818''45'resp'737''45''8776'_148 ::
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_148 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_152 v12
du_isPartialEquivalence_152 ::
  T_IsPreMetric_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_152 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_'8776''45'isEquivalence_44 (coe v1)))
-- Function.Metric.Structures.IsPreMetric._.EqC.refl
d_refl_154 :: T_IsPreMetric_104 -> AgdaAny -> AgdaAny
d_refl_154 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_'8776''45'isEquivalence_44 (coe d_isProtoMetric_112 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.EqC.reflexive
d_reflexive_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_156 v12
du_reflexive_156 ::
  T_IsPreMetric_104 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_156 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_'8776''45'isEquivalence_44 (coe v1)) v2)
-- Function.Metric.Structures.IsPreMetric._.EqC.sym
d_sym_158 ::
  T_IsPreMetric_104 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_158 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_'8776''45'isEquivalence_44 (coe d_isProtoMetric_112 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.EqC.trans
d_trans_160 ::
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_160 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_'8776''45'isEquivalence_44 (coe d_isProtoMetric_112 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_164 v12
du_isPartialEquivalence_164 ::
  T_IsPreMetric_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_164 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                  (coe v3)))))
-- Function.Metric.Structures.IsPreMetric._.Eq.refl
d_refl_166 :: T_IsPreMetric_104 -> AgdaAny -> AgdaAny
d_refl_166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0)))))
-- Function.Metric.Structures.IsPreMetric._.Eq.reflexive
d_reflexive_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsPreMetric_104 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_168 v12
du_reflexive_168 ::
  T_IsPreMetric_104 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_168 v0
  = let v1 = d_isProtoMetric_112 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                    (coe v3))
                 v4)))
-- Function.Metric.Structures.IsPreMetric._.Eq.sym
d_sym_170 ::
  T_IsPreMetric_104 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0)))))
-- Function.Metric.Structures.IsPreMetric._.Eq.trans
d_trans_172 ::
  T_IsPreMetric_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_172 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_42 (coe d_isProtoMetric_112 (coe v0)))))
-- Function.Metric.Structures.IsQuasiSemiMetric
d_IsQuasiSemiMetric_178 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_IsQuasiSemiMetric_178
  = C_constructor_252 T_IsPreMetric_104
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsQuasiSemiMetric.isPreMetric
d_isPreMetric_186 :: T_IsQuasiSemiMetric_178 -> T_IsPreMetric_104
d_isPreMetric_186 v0
  = case coe v0 of
      C_constructor_252 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsQuasiSemiMetric.0⇒≈
d_0'8658''8776'_188 ::
  T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_188 v0
  = case coe v0 of
      C_constructor_252 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsQuasiSemiMetric._.antisym
d_antisym_192 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         d_isPartialOrder_42
         (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.cong
d_cong_194 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_194 v0
  = coe
      d_cong_46
      (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0)))
-- Function.Metric.Structures.IsQuasiSemiMetric._.isEquivalence
d_isEquivalence_196 ::
  T_IsQuasiSemiMetric_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_196 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.isPartialOrder
d_isPartialOrder_198 ::
  T_IsQuasiSemiMetric_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_198 v0
  = coe
      d_isPartialOrder_42
      (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0)))
-- Function.Metric.Structures.IsQuasiSemiMetric._.isPreorder
d_isPreorder_200 ::
  T_IsQuasiSemiMetric_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         d_isPartialOrder_42
         (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.isProtoMetric
d_isProtoMetric_202 ::
  T_IsQuasiSemiMetric_178 -> T_IsProtoMetric_30
d_isProtoMetric_202 v0
  = coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))
-- Function.Metric.Structures.IsQuasiSemiMetric._.nonNegative
d_nonNegative_204 ::
  T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_204 v0
  = coe
      d_nonNegative_48
      (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0)))
-- Function.Metric.Structures.IsQuasiSemiMetric._.refl
d_refl_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny
d_refl_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_refl_206 v12
du_refl_206 :: T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny
du_refl_206 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.reflexive
d_reflexive_208 ::
  T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_208 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.trans
d_trans_210 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_210 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_212 ::
  T_IsQuasiSemiMetric_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_212 v0
  = coe
      d_'8776''45'isEquivalence_44
      (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0)))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≈⇒0
d_'8776''8658'0_214 ::
  T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_214 v0
  = coe d_'8776''8658'0_114 (coe d_isPreMetric_186 (coe v0))
-- Function.Metric.Structures.IsQuasiSemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'45''8776'_216 v12
du_'8764''45'resp'45''8776'_216 ::
  T_IsQuasiSemiMetric_178 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_216 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'691''45''8776'_218 v12
du_'8764''45'resp'691''45''8776'_218 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_218 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'737''45''8776'_220 v12
du_'8764''45'resp'737''45''8776'_220 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_220 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'45''8776'_222 v12
du_'8818''45'resp'45''8776'_222 ::
  T_IsQuasiSemiMetric_178 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_222 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'691''45''8776'_224 v12
du_'8818''45'resp'691''45''8776'_224 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_224 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'737''45''8776'_226 v12
du_'8818''45'resp'737''45''8776'_226 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_226 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_230 v12
du_isPartialEquivalence_230 ::
  T_IsQuasiSemiMetric_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_230 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_'8776''45'isEquivalence_44 (coe v2))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.refl
d_refl_232 :: T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny
d_refl_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.reflexive
d_reflexive_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_234 v12
du_reflexive_234 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_234 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_'8776''45'isEquivalence_44 (coe v2)) v3))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.sym
d_sym_236 ::
  T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_236 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.trans
d_trans_238 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_238 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_242 v12
du_isPartialEquivalence_242 ::
  T_IsQuasiSemiMetric_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_242 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                     (coe v4))))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.refl
d_refl_244 :: T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny
d_refl_244 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.reflexive
d_reflexive_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsQuasiSemiMetric_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_246 v12
du_reflexive_246 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_246 v0
  = let v1 = d_isPreMetric_186 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_112 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                       (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                       (coe v4))
                    v5))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.sym
d_sym_248 ::
  T_IsQuasiSemiMetric_178 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_248 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.trans
d_trans_250 ::
  T_IsQuasiSemiMetric_178 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_250 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe d_isProtoMetric_112 (coe d_isPreMetric_186 (coe v0))))))
-- Function.Metric.Structures.IsSemiMetric
d_IsSemiMetric_256 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_IsSemiMetric_256
  = C_constructor_334 T_IsQuasiSemiMetric_178
                      (AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsSemiMetric.isQuasiSemiMetric
d_isQuasiSemiMetric_264 ::
  T_IsSemiMetric_256 -> T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_264 v0
  = case coe v0 of
      C_constructor_334 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsSemiMetric.sym
d_sym_266 :: T_IsSemiMetric_256 -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_266 v0
  = case coe v0 of
      C_constructor_334 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsSemiMetric._.0⇒≈
d_0'8658''8776'_270 ::
  T_IsSemiMetric_256 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_270 v0
  = coe d_0'8658''8776'_188 (coe d_isQuasiSemiMetric_264 (coe v0))
-- Function.Metric.Structures.IsSemiMetric._.antisym
d_antisym_272 ::
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_272 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         d_isPartialOrder_42
         (coe
            d_isProtoMetric_112
            (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.cong
d_cong_274 ::
  T_IsSemiMetric_256 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_274 v0
  = coe
      d_cong_46
      (coe
         d_isProtoMetric_112
         (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0))))
-- Function.Metric.Structures.IsSemiMetric._.isEquivalence
d_isEquivalence_276 ::
  T_IsSemiMetric_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_276 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_112
               (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0))))))
-- Function.Metric.Structures.IsSemiMetric._.isPartialOrder
d_isPartialOrder_278 ::
  T_IsSemiMetric_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_278 v0
  = coe
      d_isPartialOrder_42
      (coe
         d_isProtoMetric_112
         (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0))))
-- Function.Metric.Structures.IsSemiMetric._.isPreMetric
d_isPreMetric_280 :: T_IsSemiMetric_256 -> T_IsPreMetric_104
d_isPreMetric_280 v0
  = coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0))
-- Function.Metric.Structures.IsSemiMetric._.isPreorder
d_isPreorder_282 ::
  T_IsSemiMetric_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_282 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         d_isPartialOrder_42
         (coe
            d_isProtoMetric_112
            (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.isProtoMetric
d_isProtoMetric_284 :: T_IsSemiMetric_256 -> T_IsProtoMetric_30
d_isProtoMetric_284 v0
  = coe
      d_isProtoMetric_112
      (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))
-- Function.Metric.Structures.IsSemiMetric._.nonNegative
d_nonNegative_286 ::
  T_IsSemiMetric_256 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_286 v0
  = coe
      d_nonNegative_48
      (coe
         d_isProtoMetric_112
         (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0))))
-- Function.Metric.Structures.IsSemiMetric._.refl
d_refl_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 -> AgdaAny -> AgdaAny
d_refl_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_refl_288 v12
du_refl_288 :: T_IsSemiMetric_256 -> AgdaAny -> AgdaAny
du_refl_288 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.reflexive
d_reflexive_290 ::
  T_IsSemiMetric_256 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_290 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_112
               (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0))))))
-- Function.Metric.Structures.IsSemiMetric._.trans
d_trans_292 ::
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_292 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_112
               (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0))))))
-- Function.Metric.Structures.IsSemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_294 ::
  T_IsSemiMetric_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_294 v0
  = coe
      d_'8776''45'isEquivalence_44
      (coe
         d_isProtoMetric_112
         (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0))))
-- Function.Metric.Structures.IsSemiMetric._.≈⇒0
d_'8776''8658'0_296 ::
  T_IsSemiMetric_256 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_296 v0
  = coe
      d_'8776''8658'0_114
      (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))
-- Function.Metric.Structures.IsSemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'45''8776'_298 v12
du_'8764''45'resp'45''8776'_298 ::
  T_IsSemiMetric_256 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_298 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'691''45''8776'_300 v12
du_'8764''45'resp'691''45''8776'_300 ::
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_300 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'737''45''8776'_302 v12
du_'8764''45'resp'737''45''8776'_302 ::
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_302 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'45''8776'_304 v12
du_'8818''45'resp'45''8776'_304 ::
  T_IsSemiMetric_256 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_304 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'691''45''8776'_306 v12
du_'8818''45'resp'691''45''8776'_306 ::
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_306 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'737''45''8776'_308 v12
du_'8818''45'resp'737''45''8776'_308 ::
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_308 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_312 v12
du_isPartialEquivalence_312 ::
  T_IsSemiMetric_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_312 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe d_'8776''45'isEquivalence_44 (coe v3)))))
-- Function.Metric.Structures.IsSemiMetric._.EqC.refl
d_refl_314 :: T_IsSemiMetric_256 -> AgdaAny -> AgdaAny
d_refl_314 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_112
            (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.EqC.reflexive
d_reflexive_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_316 v12
du_reflexive_316 ::
  T_IsSemiMetric_256 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_316 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe d_'8776''45'isEquivalence_44 (coe v3)) v4)))
-- Function.Metric.Structures.IsSemiMetric._.EqC.sym
d_sym_318 ::
  T_IsSemiMetric_256 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_318 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_112
            (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.EqC.trans
d_trans_320 ::
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_320 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_112
            (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_324 v12
du_isPartialEquivalence_324 ::
  T_IsSemiMetric_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_324 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                        (coe v5)))))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.refl
d_refl_326 :: T_IsSemiMetric_256 -> AgdaAny -> AgdaAny
d_refl_326 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_112
                  (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.reflexive
d_reflexive_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsSemiMetric_256 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_328 v12
du_reflexive_328 ::
  T_IsSemiMetric_256 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_328 v0
  = let v1 = d_isQuasiSemiMetric_264 (coe v0) in
    coe
      (let v2 = d_isPreMetric_186 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_112 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                          (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                          (coe v5))
                       v6)))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.sym
d_sym_330 ::
  T_IsSemiMetric_256 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_330 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_112
                  (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.trans
d_trans_332 ::
  T_IsSemiMetric_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_332 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_112
                  (coe d_isPreMetric_186 (coe d_isQuasiSemiMetric_264 (coe v0)))))))
-- Function.Metric.Structures.IsGeneralMetric
d_IsGeneralMetric_340 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_IsGeneralMetric_340
  = C_constructor_424 T_IsSemiMetric_256
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsGeneralMetric.isSemiMetric
d_isSemiMetric_350 :: T_IsGeneralMetric_340 -> T_IsSemiMetric_256
d_isSemiMetric_350 v0
  = case coe v0 of
      C_constructor_424 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsGeneralMetric.triangle
d_triangle_352 ::
  T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_triangle_352 v0
  = case coe v0 of
      C_constructor_424 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsGeneralMetric._.0⇒≈
d_0'8658''8776'_356 ::
  T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_356 v0
  = coe
      d_0'8658''8776'_188
      (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))
-- Function.Metric.Structures.IsGeneralMetric._.antisym
d_antisym_358 ::
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_358 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         d_isPartialOrder_42
         (coe
            d_isProtoMetric_112
            (coe
               d_isPreMetric_186
               (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.cong
d_cong_360 ::
  T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_360 v0
  = coe
      d_cong_46
      (coe
         d_isProtoMetric_112
         (coe
            d_isPreMetric_186
            (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))))
-- Function.Metric.Structures.IsGeneralMetric._.isEquivalence
d_isEquivalence_362 ::
  T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_362 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_112
               (coe
                  d_isPreMetric_186
                  (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))))))
-- Function.Metric.Structures.IsGeneralMetric._.isPartialOrder
d_isPartialOrder_364 ::
  T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_364 v0
  = coe
      d_isPartialOrder_42
      (coe
         d_isProtoMetric_112
         (coe
            d_isPreMetric_186
            (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))))
-- Function.Metric.Structures.IsGeneralMetric._.isPreMetric
d_isPreMetric_366 :: T_IsGeneralMetric_340 -> T_IsPreMetric_104
d_isPreMetric_366 v0
  = coe
      d_isPreMetric_186
      (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))
-- Function.Metric.Structures.IsGeneralMetric._.isPreorder
d_isPreorder_368 ::
  T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_368 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         d_isPartialOrder_42
         (coe
            d_isProtoMetric_112
            (coe
               d_isPreMetric_186
               (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.isProtoMetric
d_isProtoMetric_370 :: T_IsGeneralMetric_340 -> T_IsProtoMetric_30
d_isProtoMetric_370 v0
  = coe
      d_isProtoMetric_112
      (coe
         d_isPreMetric_186
         (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))
-- Function.Metric.Structures.IsGeneralMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_372 ::
  T_IsGeneralMetric_340 -> T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_372 v0
  = coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))
-- Function.Metric.Structures.IsGeneralMetric._.nonNegative
d_nonNegative_374 ::
  T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_374 v0
  = coe
      d_nonNegative_48
      (coe
         d_isProtoMetric_112
         (coe
            d_isPreMetric_186
            (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))))
-- Function.Metric.Structures.IsGeneralMetric._.refl
d_refl_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny
d_refl_376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           v13
  = du_refl_376 v13
du_refl_376 :: T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny
du_refl_376 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.reflexive
d_reflexive_378 ::
  T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_378 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_112
               (coe
                  d_isPreMetric_186
                  (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))))))
-- Function.Metric.Structures.IsGeneralMetric._.sym
d_sym_380 :: T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_380 v0 = coe d_sym_266 (coe d_isSemiMetric_350 (coe v0))
-- Function.Metric.Structures.IsGeneralMetric._.trans
d_trans_382 ::
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_382 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_112
               (coe
                  d_isPreMetric_186
                  (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))))))
-- Function.Metric.Structures.IsGeneralMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_384 ::
  T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_384 v0
  = coe
      d_'8776''45'isEquivalence_44
      (coe
         d_isProtoMetric_112
         (coe
            d_isPreMetric_186
            (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0)))))
-- Function.Metric.Structures.IsGeneralMetric._.≈⇒0
d_'8776''8658'0_386 ::
  T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_386 v0
  = coe
      d_'8776''8658'0_114
      (coe
         d_isPreMetric_186
         (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))
-- Function.Metric.Structures.IsGeneralMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 v13
  = du_'8764''45'resp'45''8776'_388 v13
du_'8764''45'resp'45''8776'_388 ::
  T_IsGeneralMetric_340 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_388 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_'8764''45'resp'691''45''8776'_390 v13
du_'8764''45'resp'691''45''8776'_390 ::
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_390 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_'8764''45'resp'737''45''8776'_392 v13
du_'8764''45'resp'737''45''8776'_392 ::
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_392 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 v13
  = du_'8818''45'resp'45''8776'_394 v13
du_'8818''45'resp'45''8776'_394 ::
  T_IsGeneralMetric_340 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_394 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_'8818''45'resp'691''45''8776'_396 v13
du_'8818''45'resp'691''45''8776'_396 ::
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_396 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_'8818''45'resp'737''45''8776'_398 v13
du_'8818''45'resp'737''45''8776'_398 ::
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_398 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_402 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 v13
  = du_isPartialEquivalence_402 v13
du_isPartialEquivalence_402 ::
  T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_402 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe d_'8776''45'isEquivalence_44 (coe v4))))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.refl
d_refl_404 :: T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny
d_refl_404 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_112
            (coe
               d_isPreMetric_186
               (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.reflexive
d_reflexive_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 v13
  = du_reflexive_406 v13
du_reflexive_406 ::
  T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_406 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe d_'8776''45'isEquivalence_44 (coe v4)) v5))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.sym
d_sym_408 ::
  T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_408 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_112
            (coe
               d_isPreMetric_186
               (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.trans
d_trans_410 ::
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_410 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_112
            (coe
               d_isPreMetric_186
               (coe d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 v13
  = du_isPartialEquivalence_414 v13
du_isPartialEquivalence_414 ::
  T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_414 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                           (coe v6))))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.refl
d_refl_416 :: T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny
d_refl_416 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_112
                  (coe
                     d_isPreMetric_186
                     (coe
                        d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.reflexive
d_reflexive_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 v13
  = du_reflexive_418 v13
du_reflexive_418 ::
  T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_418 v0
  = let v1 = d_isSemiMetric_350 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_264 (coe v1) in
       coe
         (let v3 = d_isPreMetric_186 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_112 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                             (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                             (coe v6))
                          v7))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.sym
d_sym_420 ::
  T_IsGeneralMetric_340 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_420 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_112
                  (coe
                     d_isPreMetric_186
                     (coe
                        d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.trans
d_trans_422 ::
  T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_422 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_112
                  (coe
                     d_isPreMetric_186
                     (coe
                        d_isQuasiSemiMetric_264 (coe d_isSemiMetric_350 (coe v0))))))))
