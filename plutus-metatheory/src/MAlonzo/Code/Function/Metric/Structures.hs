{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Function.Metric.Structures where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Metric.Structures.IsProtoMetric
d_IsProtoMetric_30 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_IsProtoMetric_30
  = C_IsProtoMetric'46'constructor_2109 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
                                        MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
                                        (AgdaAny ->
                                         AgdaAny ->
                                         AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsProtoMetric.isPartialOrder
d_isPartialOrder_42 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_42 v0
  = case coe v0 of
      C_IsProtoMetric'46'constructor_2109 v1 v2 v3 v4 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsProtoMetric.≈-isEquivalence
d_'8776''45'isEquivalence_44 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_44 v0
  = case coe v0 of
      C_IsProtoMetric'46'constructor_2109 v1 v2 v3 v4 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsProtoMetric.cong
d_cong_46 ::
  T_IsProtoMetric_30 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_46 v0
  = case coe v0 of
      C_IsProtoMetric'46'constructor_2109 v1 v2 v3 v4 -> coe v3
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsProtoMetric.nonNegative
d_nonNegative_48 ::
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_48 v0
  = case coe v0 of
      C_IsProtoMetric'46'constructor_2109 v1 v2 v3 v4 -> coe v4
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsProtoMetric._.antisym
d_antisym_52 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_52 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_42 (coe v0))
-- Function.Metric.Structures.IsProtoMetric._.isEquivalence
d_isEquivalence_54 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_54 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_42 (coe v0)))
-- Function.Metric.Structures.IsProtoMetric._.isPreorder
d_isPreorder_56 ::
  T_IsProtoMetric_30 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_56 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
         MAlonzo.Code.Relation.Binary.Structures.du_refl_98
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Function.Metric.Structures.IsProtoMetric._.reflexive
d_reflexive_60 ::
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_60 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_42 (coe v0)))
-- Function.Metric.Structures.IsProtoMetric._.trans
d_trans_62 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_62 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
               (coe v2))))
-- Function.Metric.Structures.IsProtoMetric._.Eq.refl
d_refl_80 :: T_IsProtoMetric_30 -> AgdaAny -> AgdaAny
d_refl_80 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                 (coe v2))
              v3))
-- Function.Metric.Structures.IsProtoMetric._.Eq.sym
d_sym_84 ::
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_84 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_42 (coe v0))))
-- Function.Metric.Structures.IsProtoMetric._.Eq.trans
d_trans_86 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_86 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
      (coe d_'8776''45'isEquivalence_44 (coe v0))
-- Function.Metric.Structures.IsProtoMetric.EqC.refl
d_refl_92 :: T_IsProtoMetric_30 -> AgdaAny -> AgdaAny
d_refl_92 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
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
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
      (coe d_'8776''45'isEquivalence_44 (coe v0)) v1
-- Function.Metric.Structures.IsProtoMetric.EqC.sym
d_sym_96 ::
  T_IsProtoMetric_30 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_96 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe d_'8776''45'isEquivalence_44 (coe v0))
-- Function.Metric.Structures.IsProtoMetric.EqC.trans
d_trans_98 ::
  T_IsProtoMetric_30 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_98 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe d_'8776''45'isEquivalence_44 (coe v0))
-- Function.Metric.Structures.IsPreMetric
d_IsPreMetric_102 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_IsPreMetric_102
  = C_IsPreMetric'46'constructor_6347 T_IsProtoMetric_30
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsPreMetric.isProtoMetric
d_isProtoMetric_110 :: T_IsPreMetric_102 -> T_IsProtoMetric_30
d_isProtoMetric_110 v0
  = case coe v0 of
      C_IsPreMetric'46'constructor_6347 v1 v2 -> coe v1
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsPreMetric.≈⇒0
d_'8776''8658'0_112 ::
  T_IsPreMetric_102 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_112 v0
  = case coe v0 of
      C_IsPreMetric'46'constructor_6347 v1 v2 -> coe v2
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsPreMetric._.antisym
d_antisym_116 ::
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_116 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.cong
d_cong_118 ::
  T_IsPreMetric_102 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_118 v0 = coe d_cong_46 (coe d_isProtoMetric_110 (coe v0))
-- Function.Metric.Structures.IsPreMetric._.isEquivalence
d_isEquivalence_120 ::
  T_IsPreMetric_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_120 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0))))
-- Function.Metric.Structures.IsPreMetric._.isPartialOrder
d_isPartialOrder_122 ::
  T_IsPreMetric_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_122 v0
  = coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0))
-- Function.Metric.Structures.IsPreMetric._.isPreorder
d_isPreorder_124 ::
  T_IsPreMetric_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_124 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.nonNegative
d_nonNegative_126 ::
  T_IsPreMetric_102 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_126 v0
  = coe d_nonNegative_48 (coe d_isProtoMetric_110 (coe v0))
-- Function.Metric.Structures.IsPreMetric._.refl
d_refl_128 ::
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
  T_IsPreMetric_102 -> AgdaAny -> AgdaAny
d_refl_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_refl_128 v12
du_refl_128 :: T_IsPreMetric_102 -> AgdaAny -> AgdaAny
du_refl_128 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.reflexive
d_reflexive_130 ::
  T_IsPreMetric_102 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_130 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0))))
-- Function.Metric.Structures.IsPreMetric._.trans
d_trans_132 ::
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_132 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0))))
-- Function.Metric.Structures.IsPreMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_134 ::
  T_IsPreMetric_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_134 v0
  = coe
      d_'8776''45'isEquivalence_44 (coe d_isProtoMetric_110 (coe v0))
-- Function.Metric.Structures.IsPreMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_136 ::
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
  T_IsPreMetric_102 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'45''8776'_136 v12
du_'8764''45'resp'45''8776'_136 ::
  T_IsPreMetric_102 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_136 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_138 ::
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
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'691''45''8776'_138 v12
du_'8764''45'resp'691''45''8776'_138 ::
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_138 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_140 ::
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
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'737''45''8776'_140 v12
du_'8764''45'resp'737''45''8776'_140 ::
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_140 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_142 ::
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
  T_IsPreMetric_102 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'45''8776'_142 v12
du_'8818''45'resp'45''8776'_142 ::
  T_IsPreMetric_102 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_142 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_144 ::
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
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'691''45''8776'_144 v12
du_'8818''45'resp'691''45''8776'_144 ::
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_144 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_146 ::
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
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'737''45''8776'_146 v12
du_'8818''45'resp'737''45''8776'_146 ::
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_146 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Function.Metric.Structures.IsPreMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_150 ::
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
  T_IsPreMetric_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_150 v12
du_isPartialEquivalence_150 ::
  T_IsPreMetric_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_150 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe d_'8776''45'isEquivalence_44 (coe v1)))
-- Function.Metric.Structures.IsPreMetric._.EqC.refl
d_refl_152 :: T_IsPreMetric_102 -> AgdaAny -> AgdaAny
d_refl_152 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_'8776''45'isEquivalence_44 (coe d_isProtoMetric_110 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.EqC.reflexive
d_reflexive_154 ::
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
  T_IsPreMetric_102 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_154 v12
du_reflexive_154 ::
  T_IsPreMetric_102 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_154 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe d_'8776''45'isEquivalence_44 (coe v1)) v2)
-- Function.Metric.Structures.IsPreMetric._.EqC.sym
d_sym_156 ::
  T_IsPreMetric_102 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_156 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_'8776''45'isEquivalence_44 (coe d_isProtoMetric_110 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.EqC.trans
d_trans_158 ::
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_158 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_'8776''45'isEquivalence_44 (coe d_isProtoMetric_110 (coe v0)))
-- Function.Metric.Structures.IsPreMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_162 ::
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
  T_IsPreMetric_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_162 v12
du_isPartialEquivalence_162 ::
  T_IsPreMetric_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_162 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v3)))))
-- Function.Metric.Structures.IsPreMetric._.Eq.refl
d_refl_164 :: T_IsPreMetric_102 -> AgdaAny -> AgdaAny
d_refl_164 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0)))))
-- Function.Metric.Structures.IsPreMetric._.Eq.reflexive
d_reflexive_166 ::
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
  T_IsPreMetric_102 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_166 v12
du_reflexive_166 ::
  T_IsPreMetric_102 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_166 v0
  = let v1 = d_isProtoMetric_110 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_42 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe v3))
                 v4)))
-- Function.Metric.Structures.IsPreMetric._.Eq.sym
d_sym_168 ::
  T_IsPreMetric_102 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_168 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0)))))
-- Function.Metric.Structures.IsPreMetric._.Eq.trans
d_trans_170 ::
  T_IsPreMetric_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_42 (coe d_isProtoMetric_110 (coe v0)))))
-- Function.Metric.Structures.IsQuasiSemiMetric
d_IsQuasiSemiMetric_174 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_IsQuasiSemiMetric_174
  = C_IsQuasiSemiMetric'46'constructor_10111 T_IsPreMetric_102
                                             (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsQuasiSemiMetric.isPreMetric
d_isPreMetric_182 :: T_IsQuasiSemiMetric_174 -> T_IsPreMetric_102
d_isPreMetric_182 v0
  = case coe v0 of
      C_IsQuasiSemiMetric'46'constructor_10111 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsQuasiSemiMetric.0⇒≈
d_0'8658''8776'_184 ::
  T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_184 v0
  = case coe v0 of
      C_IsQuasiSemiMetric'46'constructor_10111 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsQuasiSemiMetric._.antisym
d_antisym_188 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_188 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         d_isPartialOrder_42
         (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.cong
d_cong_190 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_190 v0
  = coe
      d_cong_46
      (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0)))
-- Function.Metric.Structures.IsQuasiSemiMetric._.isEquivalence
d_isEquivalence_192 ::
  T_IsQuasiSemiMetric_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.isPartialOrder
d_isPartialOrder_194 ::
  T_IsQuasiSemiMetric_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_194 v0
  = coe
      d_isPartialOrder_42
      (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0)))
-- Function.Metric.Structures.IsQuasiSemiMetric._.isPreorder
d_isPreorder_196 ::
  T_IsQuasiSemiMetric_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_196 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         d_isPartialOrder_42
         (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.isProtoMetric
d_isProtoMetric_198 ::
  T_IsQuasiSemiMetric_174 -> T_IsProtoMetric_30
d_isProtoMetric_198 v0
  = coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))
-- Function.Metric.Structures.IsQuasiSemiMetric._.nonNegative
d_nonNegative_200 ::
  T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_200 v0
  = coe
      d_nonNegative_48
      (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0)))
-- Function.Metric.Structures.IsQuasiSemiMetric._.refl
d_refl_202 ::
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
  T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny
d_refl_202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_refl_202 v12
du_refl_202 :: T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny
du_refl_202 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.reflexive
d_reflexive_204 ::
  T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_204 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.trans
d_trans_206 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_206 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_208 ::
  T_IsQuasiSemiMetric_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_208 v0
  = coe
      d_'8776''45'isEquivalence_44
      (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0)))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≈⇒0
d_'8776''8658'0_210 ::
  T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_210 v0
  = coe d_'8776''8658'0_112 (coe d_isPreMetric_182 (coe v0))
-- Function.Metric.Structures.IsQuasiSemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_212 ::
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
  T_IsQuasiSemiMetric_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'45''8776'_212 v12
du_'8764''45'resp'45''8776'_212 ::
  T_IsQuasiSemiMetric_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_212 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_214 ::
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
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'691''45''8776'_214 v12
du_'8764''45'resp'691''45''8776'_214 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_214 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_216 ::
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
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'737''45''8776'_216 v12
du_'8764''45'resp'737''45''8776'_216 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_216 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_218 ::
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
  T_IsQuasiSemiMetric_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'45''8776'_218 v12
du_'8818''45'resp'45''8776'_218 ::
  T_IsQuasiSemiMetric_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_218 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_220 ::
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
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'691''45''8776'_220 v12
du_'8818''45'resp'691''45''8776'_220 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_220 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_222 ::
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
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'737''45''8776'_222 v12
du_'8818''45'resp'737''45''8776'_222 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_222 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_226 ::
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
  T_IsQuasiSemiMetric_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_226 v12
du_isPartialEquivalence_226 ::
  T_IsQuasiSemiMetric_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_226 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe d_'8776''45'isEquivalence_44 (coe v2))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.refl
d_refl_228 :: T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny
d_refl_228 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.reflexive
d_reflexive_230 ::
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
  T_IsQuasiSemiMetric_174 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_230 v12
du_reflexive_230 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_230 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe d_'8776''45'isEquivalence_44 (coe v2)) v3))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.sym
d_sym_232 ::
  T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.EqC.trans
d_trans_234 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_238 ::
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
  T_IsQuasiSemiMetric_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_238 v12
du_isPartialEquivalence_238 ::
  T_IsQuasiSemiMetric_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_238 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                     (coe v4))))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.refl
d_refl_240 :: T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny
d_refl_240 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.reflexive
d_reflexive_242 ::
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
  T_IsQuasiSemiMetric_174 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_242 v12
du_reflexive_242 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_242 v0
  = let v1 = d_isPreMetric_182 (coe v0) in
    coe
      (let v2 = d_isProtoMetric_110 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_42 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                       (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                       (coe v4))
                    v5))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.sym
d_sym_244 ::
  T_IsQuasiSemiMetric_174 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_244 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))))))
-- Function.Metric.Structures.IsQuasiSemiMetric._.Eq.trans
d_trans_246 ::
  T_IsQuasiSemiMetric_174 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_246 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe d_isProtoMetric_110 (coe d_isPreMetric_182 (coe v0))))))
-- Function.Metric.Structures.IsSemiMetric
d_IsSemiMetric_250 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = ()
data T_IsSemiMetric_250
  = C_IsSemiMetric'46'constructor_14005 T_IsQuasiSemiMetric_174
                                        (AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsSemiMetric.isQuasiSemiMetric
d_isQuasiSemiMetric_258 ::
  T_IsSemiMetric_250 -> T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_258 v0
  = case coe v0 of
      C_IsSemiMetric'46'constructor_14005 v1 v2 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsSemiMetric.sym
d_sym_260 :: T_IsSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_260 v0
  = case coe v0 of
      C_IsSemiMetric'46'constructor_14005 v1 v2 -> coe v2
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsSemiMetric._.0⇒≈
d_0'8658''8776'_264 ::
  T_IsSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_264 v0
  = coe d_0'8658''8776'_184 (coe d_isQuasiSemiMetric_258 (coe v0))
-- Function.Metric.Structures.IsSemiMetric._.antisym
d_antisym_266 ::
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         d_isPartialOrder_42
         (coe
            d_isProtoMetric_110
            (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.cong
d_cong_268 ::
  T_IsSemiMetric_250 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_268 v0
  = coe
      d_cong_46
      (coe
         d_isProtoMetric_110
         (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0))))
-- Function.Metric.Structures.IsSemiMetric._.isEquivalence
d_isEquivalence_270 ::
  T_IsSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_270 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_110
               (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0))))))
-- Function.Metric.Structures.IsSemiMetric._.isPartialOrder
d_isPartialOrder_272 ::
  T_IsSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_272 v0
  = coe
      d_isPartialOrder_42
      (coe
         d_isProtoMetric_110
         (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0))))
-- Function.Metric.Structures.IsSemiMetric._.isPreMetric
d_isPreMetric_274 :: T_IsSemiMetric_250 -> T_IsPreMetric_102
d_isPreMetric_274 v0
  = coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0))
-- Function.Metric.Structures.IsSemiMetric._.isPreorder
d_isPreorder_276 ::
  T_IsSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_276 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         d_isPartialOrder_42
         (coe
            d_isProtoMetric_110
            (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.isProtoMetric
d_isProtoMetric_278 :: T_IsSemiMetric_250 -> T_IsProtoMetric_30
d_isProtoMetric_278 v0
  = coe
      d_isProtoMetric_110
      (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))
-- Function.Metric.Structures.IsSemiMetric._.nonNegative
d_nonNegative_280 ::
  T_IsSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_280 v0
  = coe
      d_nonNegative_48
      (coe
         d_isProtoMetric_110
         (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0))))
-- Function.Metric.Structures.IsSemiMetric._.refl
d_refl_282 ::
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
  T_IsSemiMetric_250 -> AgdaAny -> AgdaAny
d_refl_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_refl_282 v12
du_refl_282 :: T_IsSemiMetric_250 -> AgdaAny -> AgdaAny
du_refl_282 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.reflexive
d_reflexive_284 ::
  T_IsSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_284 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_110
               (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0))))))
-- Function.Metric.Structures.IsSemiMetric._.trans
d_trans_286 ::
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_286 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_110
               (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0))))))
-- Function.Metric.Structures.IsSemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_288 ::
  T_IsSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_288 v0
  = coe
      d_'8776''45'isEquivalence_44
      (coe
         d_isProtoMetric_110
         (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0))))
-- Function.Metric.Structures.IsSemiMetric._.≈⇒0
d_'8776''8658'0_290 ::
  T_IsSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_290 v0
  = coe
      d_'8776''8658'0_112
      (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))
-- Function.Metric.Structures.IsSemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_292 ::
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
  T_IsSemiMetric_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'45''8776'_292 v12
du_'8764''45'resp'45''8776'_292 ::
  T_IsSemiMetric_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_292 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_294 ::
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
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'691''45''8776'_294 v12
du_'8764''45'resp'691''45''8776'_294 ::
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_294 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_296 ::
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
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8764''45'resp'737''45''8776'_296 v12
du_'8764''45'resp'737''45''8776'_296 ::
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_296 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_298 ::
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
  T_IsSemiMetric_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'45''8776'_298 v12
du_'8818''45'resp'45''8776'_298 ::
  T_IsSemiMetric_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_298 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_300 ::
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
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'691''45''8776'_300 v12
du_'8818''45'resp'691''45''8776'_300 ::
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_300 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_302 ::
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
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12
  = du_'8818''45'resp'737''45''8776'_302 v12
du_'8818''45'resp'737''45''8776'_302 ::
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_302 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Structures.IsSemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_306 ::
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
  T_IsSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_306 v12
du_isPartialEquivalence_306 ::
  T_IsSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_306 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe d_'8776''45'isEquivalence_44 (coe v3)))))
-- Function.Metric.Structures.IsSemiMetric._.EqC.refl
d_refl_308 :: T_IsSemiMetric_250 -> AgdaAny -> AgdaAny
d_refl_308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_110
            (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.EqC.reflexive
d_reflexive_310 ::
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
  T_IsSemiMetric_250 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_310 v12
du_reflexive_310 ::
  T_IsSemiMetric_250 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_310 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe d_'8776''45'isEquivalence_44 (coe v3)) v4)))
-- Function.Metric.Structures.IsSemiMetric._.EqC.sym
d_sym_312 ::
  T_IsSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_312 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_110
            (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.EqC.trans
d_trans_314 ::
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_314 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_110
            (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_318 ::
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
  T_IsSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12
  = du_isPartialEquivalence_318 v12
du_isPartialEquivalence_318 ::
  T_IsSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_318 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                        (coe v5)))))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.refl
d_refl_320 :: T_IsSemiMetric_250 -> AgdaAny -> AgdaAny
d_refl_320 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_110
                  (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.reflexive
d_reflexive_322 ::
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
  T_IsSemiMetric_250 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12
  = du_reflexive_322 v12
du_reflexive_322 ::
  T_IsSemiMetric_250 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_322 v0
  = let v1 = d_isQuasiSemiMetric_258 (coe v0) in
    coe
      (let v2 = d_isPreMetric_182 (coe v1) in
       coe
         (let v3 = d_isProtoMetric_110 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_42 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                          (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                          (coe v5))
                       v6)))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.sym
d_sym_324 ::
  T_IsSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_324 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_110
                  (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))))))
-- Function.Metric.Structures.IsSemiMetric._.Eq.trans
d_trans_326 ::
  T_IsSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_326 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_110
                  (coe d_isPreMetric_182 (coe d_isQuasiSemiMetric_258 (coe v0)))))))
-- Function.Metric.Structures.IsGeneralMetric
d_IsGeneralMetric_332 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T_IsGeneralMetric_332
  = C_IsGeneralMetric'46'constructor_18255 T_IsSemiMetric_250
                                           (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Metric.Structures.IsGeneralMetric.isSemiMetric
d_isSemiMetric_342 :: T_IsGeneralMetric_332 -> T_IsSemiMetric_250
d_isSemiMetric_342 v0
  = case coe v0 of
      C_IsGeneralMetric'46'constructor_18255 v1 v2 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsGeneralMetric.triangle
d_triangle_344 ::
  T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_triangle_344 v0
  = case coe v0 of
      C_IsGeneralMetric'46'constructor_18255 v1 v2 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Structures.IsGeneralMetric._.0⇒≈
d_0'8658''8776'_348 ::
  T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_348 v0
  = coe
      d_0'8658''8776'_184
      (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))
-- Function.Metric.Structures.IsGeneralMetric._.antisym
d_antisym_350 ::
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         d_isPartialOrder_42
         (coe
            d_isProtoMetric_110
            (coe
               d_isPreMetric_182
               (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.cong
d_cong_352 ::
  T_IsGeneralMetric_332 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_352 v0
  = coe
      d_cong_46
      (coe
         d_isProtoMetric_110
         (coe
            d_isPreMetric_182
            (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))))
-- Function.Metric.Structures.IsGeneralMetric._.isEquivalence
d_isEquivalence_354 ::
  T_IsGeneralMetric_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_354 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_110
               (coe
                  d_isPreMetric_182
                  (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))))))
-- Function.Metric.Structures.IsGeneralMetric._.isPartialOrder
d_isPartialOrder_356 ::
  T_IsGeneralMetric_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_356 v0
  = coe
      d_isPartialOrder_42
      (coe
         d_isProtoMetric_110
         (coe
            d_isPreMetric_182
            (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))))
-- Function.Metric.Structures.IsGeneralMetric._.isPreMetric
d_isPreMetric_358 :: T_IsGeneralMetric_332 -> T_IsPreMetric_102
d_isPreMetric_358 v0
  = coe
      d_isPreMetric_182
      (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))
-- Function.Metric.Structures.IsGeneralMetric._.isPreorder
d_isPreorder_360 ::
  T_IsGeneralMetric_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_360 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         d_isPartialOrder_42
         (coe
            d_isProtoMetric_110
            (coe
               d_isPreMetric_182
               (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.isProtoMetric
d_isProtoMetric_362 :: T_IsGeneralMetric_332 -> T_IsProtoMetric_30
d_isProtoMetric_362 v0
  = coe
      d_isProtoMetric_110
      (coe
         d_isPreMetric_182
         (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))
-- Function.Metric.Structures.IsGeneralMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_364 ::
  T_IsGeneralMetric_332 -> T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_364 v0
  = coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))
-- Function.Metric.Structures.IsGeneralMetric._.nonNegative
d_nonNegative_366 ::
  T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_366 v0
  = coe
      d_nonNegative_48
      (coe
         d_isProtoMetric_110
         (coe
            d_isPreMetric_182
            (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))))
-- Function.Metric.Structures.IsGeneralMetric._.refl
d_refl_368 ::
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
  T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny
d_refl_368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           v13
  = du_refl_368 v13
du_refl_368 :: T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny
du_refl_368 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.reflexive
d_reflexive_370 ::
  T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_370 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_110
               (coe
                  d_isPreMetric_182
                  (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))))))
-- Function.Metric.Structures.IsGeneralMetric._.sym
d_sym_372 :: T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_372 v0 = coe d_sym_260 (coe d_isSemiMetric_342 (coe v0))
-- Function.Metric.Structures.IsGeneralMetric._.trans
d_trans_374 ::
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_374 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_42
            (coe
               d_isProtoMetric_110
               (coe
                  d_isPreMetric_182
                  (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))))))
-- Function.Metric.Structures.IsGeneralMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_376 ::
  T_IsGeneralMetric_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_376 v0
  = coe
      d_'8776''45'isEquivalence_44
      (coe
         d_isProtoMetric_110
         (coe
            d_isPreMetric_182
            (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0)))))
-- Function.Metric.Structures.IsGeneralMetric._.≈⇒0
d_'8776''8658'0_378 ::
  T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_378 v0
  = coe
      d_'8776''8658'0_112
      (coe
         d_isPreMetric_182
         (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))
-- Function.Metric.Structures.IsGeneralMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_380 ::
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
  T_IsGeneralMetric_332 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 v13
  = du_'8764''45'resp'45''8776'_380 v13
du_'8764''45'resp'45''8776'_380 ::
  T_IsGeneralMetric_332 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_380 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_382 ::
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
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_'8764''45'resp'691''45''8776'_382 v13
du_'8764''45'resp'691''45''8776'_382 ::
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_382 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_384 ::
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
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_'8764''45'resp'737''45''8776'_384 v13
du_'8764''45'resp'737''45''8776'_384 ::
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_384 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_386 ::
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
  T_IsGeneralMetric_332 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 ~v12 v13
  = du_'8818''45'resp'45''8776'_386 v13
du_'8818''45'resp'45''8776'_386 ::
  T_IsGeneralMetric_332 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_386 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_388 ::
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
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_'8818''45'resp'691''45''8776'_388 v13
du_'8818''45'resp'691''45''8776'_388 ::
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_388 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_390 ::
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
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 ~v12 v13
  = du_'8818''45'resp'737''45''8776'_390 v13
du_'8818''45'resp'737''45''8776'_390 ::
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_390 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_394 ::
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
  T_IsGeneralMetric_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 v13
  = du_isPartialEquivalence_394 v13
du_isPartialEquivalence_394 ::
  T_IsGeneralMetric_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_394 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe d_'8776''45'isEquivalence_44 (coe v4))))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.refl
d_refl_396 :: T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny
d_refl_396 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_110
            (coe
               d_isPreMetric_182
               (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.reflexive
d_reflexive_398 ::
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
  T_IsGeneralMetric_332 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 v13
  = du_reflexive_398 v13
du_reflexive_398 ::
  T_IsGeneralMetric_332 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_398 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe d_'8776''45'isEquivalence_44 (coe v4)) v5))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.sym
d_sym_400 ::
  T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_400 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_110
            (coe
               d_isPreMetric_182
               (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.EqC.trans
d_trans_402 ::
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_402 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         d_'8776''45'isEquivalence_44
         (coe
            d_isProtoMetric_110
            (coe
               d_isPreMetric_182
               (coe d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_406 ::
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
  T_IsGeneralMetric_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 v13
  = du_isPartialEquivalence_406 v13
du_isPartialEquivalence_406 ::
  T_IsGeneralMetric_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_406 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                           (coe v6))))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.refl
d_refl_408 :: T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny
d_refl_408 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_110
                  (coe
                     d_isPreMetric_182
                     (coe
                        d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.reflexive
d_reflexive_410 ::
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
  T_IsGeneralMetric_332 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 v13
  = du_reflexive_410 v13
du_reflexive_410 ::
  T_IsGeneralMetric_332 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_410 v0
  = let v1 = d_isSemiMetric_342 (coe v0) in
    coe
      (let v2 = d_isQuasiSemiMetric_258 (coe v1) in
       coe
         (let v3 = d_isPreMetric_182 (coe v2) in
          coe
            (let v4 = d_isProtoMetric_110 (coe v3) in
             coe
               (let v5 = d_isPartialOrder_42 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                             (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                             (coe v6))
                          v7))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.sym
d_sym_412 ::
  T_IsGeneralMetric_332 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_412 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_110
                  (coe
                     d_isPreMetric_182
                     (coe
                        d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))))))
-- Function.Metric.Structures.IsGeneralMetric._.Eq.trans
d_trans_414 ::
  T_IsGeneralMetric_332 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_414 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_42
               (coe
                  d_isProtoMetric_110
                  (coe
                     d_isPreMetric_182
                     (coe
                        d_isQuasiSemiMetric_258 (coe d_isSemiMetric_342 (coe v0))))))))
