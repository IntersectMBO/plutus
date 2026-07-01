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

module MAlonzo.Code.Function.Metric.Bundles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Metric.Structures
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Function.Metric.Bundles.ProtoMetric
d_ProtoMetric_16 a0 a1 a2 a3 a4 = ()
data T_ProtoMetric_16
  = C_constructor_118 AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
-- Function.Metric.Bundles.ProtoMetric.Carrier
d_Carrier_44 :: T_ProtoMetric_16 -> ()
d_Carrier_44 = erased
-- Function.Metric.Bundles.ProtoMetric.Image
d_Image_46 :: T_ProtoMetric_16 -> ()
d_Image_46 = erased
-- Function.Metric.Bundles.ProtoMetric._≈_
d__'8776'__48 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> ()
d__'8776'__48 = erased
-- Function.Metric.Bundles.ProtoMetric._≈ᵢ_
d__'8776''7522'__50 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__50 = erased
-- Function.Metric.Bundles.ProtoMetric._≤_
d__'8804'__52 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> ()
d__'8804'__52 = erased
-- Function.Metric.Bundles.ProtoMetric.0#
d_0'35'_54 :: T_ProtoMetric_16 -> AgdaAny
d_0'35'_54 v0
  = case coe v0 of
      C_constructor_118 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.ProtoMetric.d
d_d_56 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_56 v0
  = case coe v0 of
      C_constructor_118 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.ProtoMetric.isProtoMetric
d_isProtoMetric_58 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_58 v0
  = case coe v0 of
      C_constructor_118 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.ProtoMetric._.antisym
d_antisym_62 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_62 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe d_isProtoMetric_58 (coe v0)))
-- Function.Metric.Bundles.ProtoMetric._.cong
d_cong_64 ::
  T_ProtoMetric_16 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_64 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe d_isProtoMetric_58 (coe v0))
-- Function.Metric.Bundles.ProtoMetric._.isEquivalence
d_isEquivalence_66 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_66 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_58 (coe v0))))
-- Function.Metric.Bundles.ProtoMetric._.isPartialOrder
d_isPartialOrder_68 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_68 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe d_isProtoMetric_58 (coe v0))
-- Function.Metric.Bundles.ProtoMetric._.isPreorder
d_isPreorder_70 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_70 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe d_isProtoMetric_58 (coe v0)))
-- Function.Metric.Bundles.ProtoMetric._.nonNegative
d_nonNegative_72 ::
  T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_72 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe d_isProtoMetric_58 (coe v0))
-- Function.Metric.Bundles.ProtoMetric._.refl
d_refl_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 -> AgdaAny -> AgdaAny
d_refl_74 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_74 v5
du_refl_74 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny
du_refl_74 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Bundles.ProtoMetric._.reflexive
d_reflexive_76 ::
  T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_76 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_58 (coe v0))))
-- Function.Metric.Bundles.ProtoMetric._.trans
d_trans_78 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_58 (coe v0))))
-- Function.Metric.Bundles.ProtoMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_80 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_80 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe d_isProtoMetric_58 (coe v0))
-- Function.Metric.Bundles.ProtoMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_82 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_82 v5
du_'8764''45'resp'45''8776'_82 ::
  T_ProtoMetric_16 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_82 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Bundles.ProtoMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_84 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_84 v5
du_'8764''45'resp'691''45''8776'_84 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_84 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Bundles.ProtoMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_86 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_86 v5
du_'8764''45'resp'737''45''8776'_86 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_86 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Bundles.ProtoMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_88 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_88 v5
du_'8818''45'resp'45''8776'_88 ::
  T_ProtoMetric_16 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_88 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Bundles.ProtoMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_90 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_90 v5
du_'8818''45'resp'691''45''8776'_90 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_90 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Bundles.ProtoMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_92 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_92 v5
du_'8818''45'resp'737''45''8776'_92 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_92 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Function.Metric.Bundles.ProtoMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_96 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_96 v5
du_isPartialEquivalence_96 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_96 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
            (coe v1)))
-- Function.Metric.Bundles.ProtoMetric._.EqC.refl
d_refl_98 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny
d_refl_98 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_58 (coe v0)))
-- Function.Metric.Bundles.ProtoMetric._.EqC.reflexive
d_reflexive_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_100 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_100 v5
du_reflexive_100 ::
  T_ProtoMetric_16 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_100 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe
              MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
              (coe v1))
           v2)
-- Function.Metric.Bundles.ProtoMetric._.EqC.sym
d_sym_102 ::
  T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_102 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_58 (coe v0)))
-- Function.Metric.Bundles.ProtoMetric._.EqC.trans
d_trans_104 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_104 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_58 (coe v0)))
-- Function.Metric.Bundles.ProtoMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_108 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_108 v5
du_isPartialEquivalence_108 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_108 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
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
-- Function.Metric.Bundles.ProtoMetric._.Eq.refl
d_refl_110 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny
d_refl_110 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe d_isProtoMetric_58 (coe v0)))))
-- Function.Metric.Bundles.ProtoMetric._.Eq.reflexive
d_reflexive_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_16 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_112 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_112 v5
du_reflexive_112 ::
  T_ProtoMetric_16 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_112 v0
  = let v1 = d_isProtoMetric_58 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                 (coe v1) in
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
-- Function.Metric.Bundles.ProtoMetric._.Eq.sym
d_sym_114 ::
  T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_114 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe d_isProtoMetric_58 (coe v0)))))
-- Function.Metric.Bundles.ProtoMetric._.Eq.trans
d_trans_116 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_116 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe d_isProtoMetric_58 (coe v0)))))
-- Function.Metric.Bundles.PreMetric
d_PreMetric_130 a0 a1 a2 a3 a4 = ()
data T_PreMetric_130
  = C_constructor_238 AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
-- Function.Metric.Bundles.PreMetric.Carrier
d_Carrier_158 :: T_PreMetric_130 -> ()
d_Carrier_158 = erased
-- Function.Metric.Bundles.PreMetric.Image
d_Image_160 :: T_PreMetric_130 -> ()
d_Image_160 = erased
-- Function.Metric.Bundles.PreMetric._≈_
d__'8776'__162 :: T_PreMetric_130 -> AgdaAny -> AgdaAny -> ()
d__'8776'__162 = erased
-- Function.Metric.Bundles.PreMetric._≈ᵢ_
d__'8776''7522'__164 :: T_PreMetric_130 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__164 = erased
-- Function.Metric.Bundles.PreMetric._≤_
d__'8804'__166 :: T_PreMetric_130 -> AgdaAny -> AgdaAny -> ()
d__'8804'__166 = erased
-- Function.Metric.Bundles.PreMetric.0#
d_0'35'_168 :: T_PreMetric_130 -> AgdaAny
d_0'35'_168 v0
  = case coe v0 of
      C_constructor_238 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.PreMetric.d
d_d_170 :: T_PreMetric_130 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_170 v0
  = case coe v0 of
      C_constructor_238 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.PreMetric.isPreMetric
d_isPreMetric_172 ::
  T_PreMetric_130 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_172 v0
  = case coe v0 of
      C_constructor_238 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.PreMetric._.antisym
d_antisym_176 ::
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_172 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.cong
d_cong_178 ::
  T_PreMetric_130 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_178 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_172 (coe v0)))
-- Function.Metric.Bundles.PreMetric._.isEquivalence
d_isEquivalence_180 ::
  T_PreMetric_130 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe d_isPreMetric_172 (coe v0)))))
-- Function.Metric.Bundles.PreMetric._.isPartialOrder
d_isPartialOrder_182 ::
  T_PreMetric_130 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_182 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_172 (coe v0)))
-- Function.Metric.Bundles.PreMetric._.isPreorder
d_isPreorder_184 ::
  T_PreMetric_130 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_184 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_172 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.isProtoMetric
d_isProtoMetric_186 ::
  T_PreMetric_130 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_186 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe d_isPreMetric_172 (coe v0))
-- Function.Metric.Bundles.PreMetric._.nonNegative
d_nonNegative_188 ::
  T_PreMetric_130 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_188 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_172 (coe v0)))
-- Function.Metric.Bundles.PreMetric._.refl
d_refl_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 -> AgdaAny -> AgdaAny
d_refl_190 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_190 v5
du_refl_190 :: T_PreMetric_130 -> AgdaAny -> AgdaAny
du_refl_190 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.reflexive
d_reflexive_192 ::
  T_PreMetric_130 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe d_isPreMetric_172 (coe v0)))))
-- Function.Metric.Bundles.PreMetric._.trans
d_trans_194 ::
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_194 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe d_isPreMetric_172 (coe v0)))))
-- Function.Metric.Bundles.PreMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_196 ::
  T_PreMetric_130 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_196 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_172 (coe v0)))
-- Function.Metric.Bundles.PreMetric._.≈⇒0
d_'8776''8658'0_198 ::
  T_PreMetric_130 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_198 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''8658'0_114
      (coe d_isPreMetric_172 (coe v0))
-- Function.Metric.Bundles.PreMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_200 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_200 v5
du_'8764''45'resp'45''8776'_200 ::
  T_PreMetric_130 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_200 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_202 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_202 v5
du_'8764''45'resp'691''45''8776'_202 ::
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_202 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_204 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_204 v5
du_'8764''45'resp'737''45''8776'_204 ::
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_204 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_206 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_206 v5
du_'8818''45'resp'45''8776'_206 ::
  T_PreMetric_130 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_206 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_208 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_208 v5
du_'8818''45'resp'691''45''8776'_208 ::
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_208 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_210 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_210 v5
du_'8818''45'resp'737''45''8776'_210 ::
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_210 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_214 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_214 v5
du_isPartialEquivalence_214 ::
  T_PreMetric_130 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_214 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
               (coe v2))))
-- Function.Metric.Bundles.PreMetric._.EqC.refl
d_refl_216 :: T_PreMetric_130 -> AgdaAny -> AgdaAny
d_refl_216 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_172 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.EqC.reflexive
d_reflexive_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_218 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_218 v5
du_reflexive_218 ::
  T_PreMetric_130 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_218 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                 (coe v2))
              v3))
-- Function.Metric.Bundles.PreMetric._.EqC.sym
d_sym_220 ::
  T_PreMetric_130 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_220 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_172 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.EqC.trans
d_trans_222 ::
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_222 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_172 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_226 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_226 v5
du_isPartialEquivalence_226 ::
  T_PreMetric_130 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_226 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
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
-- Function.Metric.Bundles.PreMetric._.Eq.refl
d_refl_228 :: T_PreMetric_130 -> AgdaAny -> AgdaAny
d_refl_228 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe d_isPreMetric_172 (coe v0))))))
-- Function.Metric.Bundles.PreMetric._.Eq.reflexive
d_reflexive_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_230 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_230 v5
du_reflexive_230 ::
  T_PreMetric_130 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_230 v0
  = let v1 = d_isPreMetric_172 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
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
-- Function.Metric.Bundles.PreMetric._.Eq.sym
d_sym_232 ::
  T_PreMetric_130 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe d_isPreMetric_172 (coe v0))))))
-- Function.Metric.Bundles.PreMetric._.Eq.trans
d_trans_234 ::
  T_PreMetric_130 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe d_isPreMetric_172 (coe v0))))))
-- Function.Metric.Bundles.PreMetric.protoMetric
d_protoMetric_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_130 -> T_ProtoMetric_16
d_protoMetric_236 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_protoMetric_236 v5
du_protoMetric_236 :: T_PreMetric_130 -> T_ProtoMetric_16
du_protoMetric_236 v0
  = coe
      C_constructor_118 (d_0'35'_168 (coe v0)) (d_d_170 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_172 (coe v0)))
-- Function.Metric.Bundles.QuasiSemiMetric
d_QuasiSemiMetric_250 a0 a1 a2 a3 a4 = ()
data T_QuasiSemiMetric_250
  = C_constructor_366 AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
-- Function.Metric.Bundles.QuasiSemiMetric.Carrier
d_Carrier_278 :: T_QuasiSemiMetric_250 -> ()
d_Carrier_278 = erased
-- Function.Metric.Bundles.QuasiSemiMetric.Image
d_Image_280 :: T_QuasiSemiMetric_250 -> ()
d_Image_280 = erased
-- Function.Metric.Bundles.QuasiSemiMetric._≈_
d__'8776'__282 :: T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> ()
d__'8776'__282 = erased
-- Function.Metric.Bundles.QuasiSemiMetric._≈ᵢ_
d__'8776''7522'__284 ::
  T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__284 = erased
-- Function.Metric.Bundles.QuasiSemiMetric._≤_
d__'8804'__286 :: T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> ()
d__'8804'__286 = erased
-- Function.Metric.Bundles.QuasiSemiMetric.0#
d_0'35'_288 :: T_QuasiSemiMetric_250 -> AgdaAny
d_0'35'_288 v0
  = case coe v0 of
      C_constructor_366 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.QuasiSemiMetric.d
d_d_290 :: T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_290 v0
  = case coe v0 of
      C_constructor_366 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.QuasiSemiMetric.isQuasiSemiMetric
d_isQuasiSemiMetric_292 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_292 v0
  = case coe v0 of
      C_constructor_366 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.QuasiSemiMetric._.0⇒≈
d_0'8658''8776'_296 ::
  T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_296 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe d_isQuasiSemiMetric_292 (coe v0))
-- Function.Metric.Bundles.QuasiSemiMetric._.antisym
d_antisym_298 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_298 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_292 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.cong
d_cong_300 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_300 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe d_isQuasiSemiMetric_292 (coe v0))))
-- Function.Metric.Bundles.QuasiSemiMetric._.isEquivalence
d_isEquivalence_302 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_302 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe d_isQuasiSemiMetric_292 (coe v0))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.isPartialOrder
d_isPartialOrder_304 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_304 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe d_isQuasiSemiMetric_292 (coe v0))))
-- Function.Metric.Bundles.QuasiSemiMetric._.isPreMetric
d_isPreMetric_306 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_306 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe d_isQuasiSemiMetric_292 (coe v0))
-- Function.Metric.Bundles.QuasiSemiMetric._.isPreorder
d_isPreorder_308 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_292 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.isProtoMetric
d_isProtoMetric_310 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_310 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe d_isQuasiSemiMetric_292 (coe v0)))
-- Function.Metric.Bundles.QuasiSemiMetric._.nonNegative
d_nonNegative_312 ::
  T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_312 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe d_isQuasiSemiMetric_292 (coe v0))))
-- Function.Metric.Bundles.QuasiSemiMetric._.refl
d_refl_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny
d_refl_314 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_314 v5
du_refl_314 :: T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny
du_refl_314 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.reflexive
d_reflexive_316 ::
  T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_316 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe d_isQuasiSemiMetric_292 (coe v0))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.trans
d_trans_318 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_318 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe d_isQuasiSemiMetric_292 (coe v0))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_320 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_320 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe d_isQuasiSemiMetric_292 (coe v0))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≈⇒0
d_'8776''8658'0_322 ::
  T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_322 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''8658'0_114
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe d_isQuasiSemiMetric_292 (coe v0)))
-- Function.Metric.Bundles.QuasiSemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_324 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_324 v5
du_'8764''45'resp'45''8776'_324 ::
  T_QuasiSemiMetric_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_324 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_326 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_326 v5
du_'8764''45'resp'691''45''8776'_326 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_326 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_328 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_328 v5
du_'8764''45'resp'737''45''8776'_328 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_328 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_330 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_330 v5
du_'8818''45'resp'45''8776'_330 ::
  T_QuasiSemiMetric_250 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_330 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_332 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_332 v5
du_'8818''45'resp'691''45''8776'_332 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_332 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_334 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_334 v5
du_'8818''45'resp'737''45''8776'_334 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_334 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_338 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_338 v5
du_isPartialEquivalence_338 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_338 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                  (coe v3)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.refl
d_refl_340 :: T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny
d_refl_340 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_292 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.reflexive
d_reflexive_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_342 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_342 v5
du_reflexive_342 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_342 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                    (coe v3))
                 v4)))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.sym
d_sym_344 ::
  T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_344 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_292 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.trans
d_trans_346 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_346 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_292 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_350 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_350 v5
du_isPartialEquivalence_350 ::
  T_QuasiSemiMetric_250 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_350 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
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
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.refl
d_refl_352 :: T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny
d_refl_352 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe d_isQuasiSemiMetric_292 (coe v0)))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.reflexive
d_reflexive_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_354 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_354 v5
du_reflexive_354 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_354 v0
  = let v1 = d_isQuasiSemiMetric_292 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
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
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.sym
d_sym_356 ::
  T_QuasiSemiMetric_250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_356 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe d_isQuasiSemiMetric_292 (coe v0)))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.trans
d_trans_358 ::
  T_QuasiSemiMetric_250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_358 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe d_isQuasiSemiMetric_292 (coe v0)))))))
-- Function.Metric.Bundles.QuasiSemiMetric.preMetric
d_preMetric_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 -> T_PreMetric_130
d_preMetric_360 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_preMetric_360 v5
du_preMetric_360 :: T_QuasiSemiMetric_250 -> T_PreMetric_130
du_preMetric_360 v0
  = coe
      C_constructor_238 (d_0'35'_288 (coe v0)) (d_d_290 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe d_isQuasiSemiMetric_292 (coe v0)))
-- Function.Metric.Bundles.QuasiSemiMetric._.protoMetric
d_protoMetric_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_250 -> T_ProtoMetric_16
d_protoMetric_364 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_protoMetric_364 v5
du_protoMetric_364 :: T_QuasiSemiMetric_250 -> T_ProtoMetric_16
du_protoMetric_364 v0
  = coe du_protoMetric_236 (coe du_preMetric_360 (coe v0))
-- Function.Metric.Bundles.SemiMetric
d_SemiMetric_378 a0 a1 a2 a3 a4 = ()
data T_SemiMetric_378
  = C_constructor_500 AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
-- Function.Metric.Bundles.SemiMetric.Carrier
d_Carrier_406 :: T_SemiMetric_378 -> ()
d_Carrier_406 = erased
-- Function.Metric.Bundles.SemiMetric.Image
d_Image_408 :: T_SemiMetric_378 -> ()
d_Image_408 = erased
-- Function.Metric.Bundles.SemiMetric._≈_
d__'8776'__410 :: T_SemiMetric_378 -> AgdaAny -> AgdaAny -> ()
d__'8776'__410 = erased
-- Function.Metric.Bundles.SemiMetric._≈ᵢ_
d__'8776''7522'__412 ::
  T_SemiMetric_378 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__412 = erased
-- Function.Metric.Bundles.SemiMetric._≤_
d__'8804'__414 :: T_SemiMetric_378 -> AgdaAny -> AgdaAny -> ()
d__'8804'__414 = erased
-- Function.Metric.Bundles.SemiMetric.0#
d_0'35'_416 :: T_SemiMetric_378 -> AgdaAny
d_0'35'_416 v0
  = case coe v0 of
      C_constructor_500 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.SemiMetric.d
d_d_418 :: T_SemiMetric_378 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_418 v0
  = case coe v0 of
      C_constructor_500 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.SemiMetric.isSemiMetric
d_isSemiMetric_420 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
d_isSemiMetric_420 v0
  = case coe v0 of
      C_constructor_500 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.SemiMetric._.0⇒≈
d_0'8658''8776'_424 ::
  T_SemiMetric_378 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_424 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe d_isSemiMetric_420 (coe v0)))
-- Function.Metric.Bundles.SemiMetric._.antisym
d_antisym_426 ::
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_426 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe d_isSemiMetric_420 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.cong
d_cong_428 ::
  T_SemiMetric_378 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_428 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe d_isSemiMetric_420 (coe v0)))))
-- Function.Metric.Bundles.SemiMetric._.isEquivalence
d_isEquivalence_430 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_430 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                     (coe d_isSemiMetric_420 (coe v0)))))))
-- Function.Metric.Bundles.SemiMetric._.isPartialOrder
d_isPartialOrder_432 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_432 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe d_isSemiMetric_420 (coe v0)))))
-- Function.Metric.Bundles.SemiMetric._.isPreMetric
d_isPreMetric_434 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_434 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe d_isSemiMetric_420 (coe v0)))
-- Function.Metric.Bundles.SemiMetric._.isPreorder
d_isPreorder_436 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_436 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe d_isSemiMetric_420 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.isProtoMetric
d_isProtoMetric_438 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_438 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe d_isSemiMetric_420 (coe v0))))
-- Function.Metric.Bundles.SemiMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_440 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_440 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
      (coe d_isSemiMetric_420 (coe v0))
-- Function.Metric.Bundles.SemiMetric._.nonNegative
d_nonNegative_442 ::
  T_SemiMetric_378 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_442 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe d_isSemiMetric_420 (coe v0)))))
-- Function.Metric.Bundles.SemiMetric._.refl
d_refl_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 -> AgdaAny -> AgdaAny
d_refl_444 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_444 v5
du_refl_444 :: T_SemiMetric_378 -> AgdaAny -> AgdaAny
du_refl_444 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.reflexive
d_reflexive_446 ::
  T_SemiMetric_378 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_446 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                     (coe d_isSemiMetric_420 (coe v0)))))))
-- Function.Metric.Bundles.SemiMetric._.sym
d_sym_448 :: T_SemiMetric_378 -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_448 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_sym_266
      (coe d_isSemiMetric_420 (coe v0))
-- Function.Metric.Bundles.SemiMetric._.trans
d_trans_450 ::
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_450 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                     (coe d_isSemiMetric_420 (coe v0)))))))
-- Function.Metric.Bundles.SemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_452 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_452 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe d_isSemiMetric_420 (coe v0)))))
-- Function.Metric.Bundles.SemiMetric._.≈⇒0
d_'8776''8658'0_454 ::
  T_SemiMetric_378 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_454 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''8658'0_114
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe d_isSemiMetric_420 (coe v0))))
-- Function.Metric.Bundles.SemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_456 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_456 v5
du_'8764''45'resp'45''8776'_456 ::
  T_SemiMetric_378 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_456 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_458 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_458 v5
du_'8764''45'resp'691''45''8776'_458 ::
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_458 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_460 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_460 v5
du_'8764''45'resp'737''45''8776'_460 ::
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_460 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_462 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_462 v5
du_'8818''45'resp'45''8776'_462 ::
  T_SemiMetric_378 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_462 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_464 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_464 v5
du_'8818''45'resp'691''45''8776'_464 ::
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_464 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_466 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_466 v5
du_'8818''45'resp'737''45''8776'_466 ::
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_466 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_470 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_470 v5
du_isPartialEquivalence_470 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_470 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                     (coe v4))))))
-- Function.Metric.Bundles.SemiMetric._.EqC.refl
d_refl_472 :: T_SemiMetric_378 -> AgdaAny -> AgdaAny
d_refl_472 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe d_isSemiMetric_420 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.EqC.reflexive
d_reflexive_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_474 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_474 v5
du_reflexive_474 ::
  T_SemiMetric_378 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_474 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe
                       MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                       (coe v4))
                    v5))))
-- Function.Metric.Bundles.SemiMetric._.EqC.sym
d_sym_476 ::
  T_SemiMetric_378 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_476 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe d_isSemiMetric_420 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.EqC.trans
d_trans_478 ::
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_478 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe d_isSemiMetric_420 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_482 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_482 v5
du_isPartialEquivalence_482 ::
  T_SemiMetric_378 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_482 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
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
-- Function.Metric.Bundles.SemiMetric._.Eq.refl
d_refl_484 :: T_SemiMetric_378 -> AgdaAny -> AgdaAny
d_refl_484 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                        (coe d_isSemiMetric_420 (coe v0))))))))
-- Function.Metric.Bundles.SemiMetric._.Eq.reflexive
d_reflexive_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_486 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_486 v5
du_reflexive_486 ::
  T_SemiMetric_378 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_486 v0
  = let v1 = d_isSemiMetric_420 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
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
-- Function.Metric.Bundles.SemiMetric._.Eq.sym
d_sym_488 ::
  T_SemiMetric_378 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_488 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                        (coe d_isSemiMetric_420 (coe v0))))))))
-- Function.Metric.Bundles.SemiMetric._.Eq.trans
d_trans_490 ::
  T_SemiMetric_378 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_490 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                        (coe d_isSemiMetric_420 (coe v0))))))))
-- Function.Metric.Bundles.SemiMetric.quasiSemiMetric
d_quasiSemiMetric_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 -> T_QuasiSemiMetric_250
d_quasiSemiMetric_492 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_quasiSemiMetric_492 v5
du_quasiSemiMetric_492 :: T_SemiMetric_378 -> T_QuasiSemiMetric_250
du_quasiSemiMetric_492 v0
  = coe
      C_constructor_366 (d_0'35'_416 (coe v0)) (d_d_418 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe d_isSemiMetric_420 (coe v0)))
-- Function.Metric.Bundles.SemiMetric._.preMetric
d_preMetric_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 -> T_PreMetric_130
d_preMetric_496 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_preMetric_496 v5
du_preMetric_496 :: T_SemiMetric_378 -> T_PreMetric_130
du_preMetric_496 v0
  = coe du_preMetric_360 (coe du_quasiSemiMetric_492 (coe v0))
-- Function.Metric.Bundles.SemiMetric._.protoMetric
d_protoMetric_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_378 -> T_ProtoMetric_16
d_protoMetric_498 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_protoMetric_498 v5
du_protoMetric_498 :: T_SemiMetric_378 -> T_ProtoMetric_16
du_protoMetric_498 v0
  = let v1 = coe du_quasiSemiMetric_492 (coe v0) in
    coe (coe du_protoMetric_236 (coe du_preMetric_360 (coe v1)))
-- Function.Metric.Bundles.GeneralMetric
d_GeneralMetric_512 a0 a1 a2 a3 a4 = ()
data T_GeneralMetric_512
  = C_constructor_644 AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340
-- Function.Metric.Bundles.GeneralMetric.Carrier
d_Carrier_542 :: T_GeneralMetric_512 -> ()
d_Carrier_542 = erased
-- Function.Metric.Bundles.GeneralMetric.Image
d_Image_544 :: T_GeneralMetric_512 -> ()
d_Image_544 = erased
-- Function.Metric.Bundles.GeneralMetric._≈_
d__'8776'__546 :: T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> ()
d__'8776'__546 = erased
-- Function.Metric.Bundles.GeneralMetric._≈ᵢ_
d__'8776''7522'__548 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__548 = erased
-- Function.Metric.Bundles.GeneralMetric._≤_
d__'8804'__550 :: T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> ()
d__'8804'__550 = erased
-- Function.Metric.Bundles.GeneralMetric.0#
d_0'35'_552 :: T_GeneralMetric_512 -> AgdaAny
d_0'35'_552 v0
  = case coe v0 of
      C_constructor_644 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.GeneralMetric._∙_
d__'8729'__554 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__554 v0
  = case coe v0 of
      C_constructor_644 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.GeneralMetric.d
d_d_556 :: T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_556 v0
  = case coe v0 of
      C_constructor_644 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.GeneralMetric.isGeneralMetric
d_isGeneralMetric_558 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340
d_isGeneralMetric_558 v0
  = case coe v0 of
      C_constructor_644 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.GeneralMetric._.0⇒≈
d_0'8658''8776'_562 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_562 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe d_isGeneralMetric_558 (coe v0))))
-- Function.Metric.Bundles.GeneralMetric._.antisym
d_antisym_564 ::
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_564 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                     (coe d_isGeneralMetric_558 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.cong
d_cong_566 ::
  T_GeneralMetric_512 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_566 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                  (coe d_isGeneralMetric_558 (coe v0))))))
-- Function.Metric.Bundles.GeneralMetric._.isEquivalence
d_isEquivalence_568 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_568 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                        (coe d_isGeneralMetric_558 (coe v0))))))))
-- Function.Metric.Bundles.GeneralMetric._.isPartialOrder
d_isPartialOrder_570 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_570 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                  (coe d_isGeneralMetric_558 (coe v0))))))
-- Function.Metric.Bundles.GeneralMetric._.isPreMetric
d_isPreMetric_572 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_572 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe d_isGeneralMetric_558 (coe v0))))
-- Function.Metric.Bundles.GeneralMetric._.isPreorder
d_isPreorder_574 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_574 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                     (coe d_isGeneralMetric_558 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.isProtoMetric
d_isProtoMetric_576 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_576 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
               (coe d_isGeneralMetric_558 (coe v0)))))
-- Function.Metric.Bundles.GeneralMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_578 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_578 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe d_isGeneralMetric_558 (coe v0)))
-- Function.Metric.Bundles.GeneralMetric._.isSemiMetric
d_isSemiMetric_580 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
d_isSemiMetric_580 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
      (coe d_isGeneralMetric_558 (coe v0))
-- Function.Metric.Bundles.GeneralMetric._.nonNegative
d_nonNegative_582 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_582 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                  (coe d_isGeneralMetric_558 (coe v0))))))
-- Function.Metric.Bundles.GeneralMetric._.refl
d_refl_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny
d_refl_584 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_584 v5
du_refl_584 :: T_GeneralMetric_512 -> AgdaAny -> AgdaAny
du_refl_584 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.reflexive
d_reflexive_586 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_586 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                        (coe d_isGeneralMetric_558 (coe v0))))))))
-- Function.Metric.Bundles.GeneralMetric._.sym
d_sym_588 :: T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_588 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_sym_266
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe d_isGeneralMetric_558 (coe v0)))
-- Function.Metric.Bundles.GeneralMetric._.trans
d_trans_590 ::
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_590 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                        (coe d_isGeneralMetric_558 (coe v0))))))))
-- Function.Metric.Bundles.GeneralMetric._.triangle
d_triangle_592 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_triangle_592 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_triangle_352
      (coe d_isGeneralMetric_558 (coe v0))
-- Function.Metric.Bundles.GeneralMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_594 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_594 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                  (coe d_isGeneralMetric_558 (coe v0))))))
-- Function.Metric.Bundles.GeneralMetric._.≈⇒0
d_'8776''8658'0_596 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_596 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''8658'0_114
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
               (coe d_isGeneralMetric_558 (coe v0)))))
-- Function.Metric.Bundles.GeneralMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_598 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_598 v5
du_'8764''45'resp'45''8776'_598 ::
  T_GeneralMetric_512 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_598 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_600 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_600 v5
du_'8764''45'resp'691''45''8776'_600 ::
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_600 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_602 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_602 v5
du_'8764''45'resp'737''45''8776'_602 ::
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_602 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_604 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_604 v5
du_'8818''45'resp'45''8776'_604 ::
  T_GeneralMetric_512 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_604 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_606 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_606 v5
du_'8818''45'resp'691''45''8776'_606 ::
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_606 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_608 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_608 v5
du_'8818''45'resp'737''45''8776'_608 ::
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_608 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_612 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_612 v5
du_isPartialEquivalence_612 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_612 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                        (coe v5)))))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.refl
d_refl_614 :: T_GeneralMetric_512 -> AgdaAny -> AgdaAny
d_refl_614 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                     (coe d_isGeneralMetric_558 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.reflexive
d_reflexive_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_616 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_616 v5
du_reflexive_616 ::
  T_GeneralMetric_512 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_616 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe
                          MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                          (coe v5))
                       v6)))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.sym
d_sym_618 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_618 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                     (coe d_isGeneralMetric_558 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.trans
d_trans_620 ::
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_620 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                     (coe d_isGeneralMetric_558 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_624 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_624 v5
du_isPartialEquivalence_624 ::
  T_GeneralMetric_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_624 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                                (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                              (coe v7)))))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.refl
d_refl_626 :: T_GeneralMetric_512 -> AgdaAny -> AgdaAny
d_refl_626 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                        (coe
                           MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                           (coe d_isGeneralMetric_558 (coe v0)))))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.reflexive
d_reflexive_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_628 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_628 v5
du_reflexive_628 ::
  T_GeneralMetric_512 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_628 v0
  = let v1 = d_isGeneralMetric_558 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                                (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                                (coe v7))
                             v8)))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.sym
d_sym_630 ::
  T_GeneralMetric_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_630 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                        (coe
                           MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                           (coe d_isGeneralMetric_558 (coe v0)))))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.trans
d_trans_632 ::
  T_GeneralMetric_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_632 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
                        (coe
                           MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                           (coe d_isGeneralMetric_558 (coe v0)))))))))
-- Function.Metric.Bundles.GeneralMetric.semiMetric
d_semiMetric_634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 -> T_SemiMetric_378
d_semiMetric_634 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_semiMetric_634 v5
du_semiMetric_634 :: T_GeneralMetric_512 -> T_SemiMetric_378
du_semiMetric_634 v0
  = coe
      C_constructor_500 (d_0'35'_552 (coe v0)) (d_d_556 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe d_isGeneralMetric_558 (coe v0)))
-- Function.Metric.Bundles.GeneralMetric._.preMetric
d_preMetric_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 -> T_PreMetric_130
d_preMetric_638 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_preMetric_638 v5
du_preMetric_638 :: T_GeneralMetric_512 -> T_PreMetric_130
du_preMetric_638 v0
  = let v1 = coe du_semiMetric_634 (coe v0) in
    coe (coe du_preMetric_360 (coe du_quasiSemiMetric_492 (coe v1)))
-- Function.Metric.Bundles.GeneralMetric._.protoMetric
d_protoMetric_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 -> T_ProtoMetric_16
d_protoMetric_640 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_protoMetric_640 v5
du_protoMetric_640 :: T_GeneralMetric_512 -> T_ProtoMetric_16
du_protoMetric_640 v0
  = let v1 = coe du_semiMetric_634 (coe v0) in
    coe
      (let v2 = coe du_quasiSemiMetric_492 (coe v1) in
       coe (coe du_protoMetric_236 (coe du_preMetric_360 (coe v2))))
-- Function.Metric.Bundles.GeneralMetric._.quasiSemiMetric
d_quasiSemiMetric_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_512 -> T_QuasiSemiMetric_250
d_quasiSemiMetric_642 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_quasiSemiMetric_642 v5
du_quasiSemiMetric_642 ::
  T_GeneralMetric_512 -> T_QuasiSemiMetric_250
du_quasiSemiMetric_642 v0
  = coe du_quasiSemiMetric_492 (coe du_semiMetric_634 (coe v0))
