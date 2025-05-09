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

module MAlonzo.Code.Function.Metric.Bundles where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Metric.Structures qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Metric.Bundles.ProtoMetric
d_ProtoMetric_16 a0 a1 a2 a3 a4 = ()
data T_ProtoMetric_16
  = C_ProtoMetric'46'constructor_967 AgdaAny
                                     (AgdaAny -> AgdaAny -> AgdaAny)
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
      C_ProtoMetric'46'constructor_967 v6 v7 v8 -> coe v6
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.ProtoMetric.d
d_d_56 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_56 v0
  = case coe v0 of
      C_ProtoMetric'46'constructor_967 v6 v7 v8 -> coe v7
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.ProtoMetric.isProtoMetric
d_isProtoMetric_58 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_58 v0
  = case coe v0 of
      C_ProtoMetric'46'constructor_967 v6 v7 v8 -> coe v8
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.ProtoMetric._.antisym
d_antisym_62 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_62 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_66 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_58 (coe v0))))
-- Function.Metric.Bundles.ProtoMetric._.isPartialOrder
d_isPartialOrder_68 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_68 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe d_isProtoMetric_58 (coe v0))
-- Function.Metric.Bundles.ProtoMetric._.isPreorder
d_isPreorder_70 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_70 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Function.Metric.Bundles.ProtoMetric._.reflexive
d_reflexive_76 ::
  T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_76 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_58 (coe v0))))
-- Function.Metric.Bundles.ProtoMetric._.trans
d_trans_78 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_58 (coe v0))))
-- Function.Metric.Bundles.ProtoMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_80 ::
  T_ProtoMetric_16 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
            (coe v1)))
-- Function.Metric.Bundles.ProtoMetric._.EqC.refl
d_refl_98 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny
d_refl_98 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
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
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
              (coe v1))
           v2)
-- Function.Metric.Bundles.ProtoMetric._.EqC.sym
d_sym_102 ::
  T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_102 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_58 (coe v0)))
-- Function.Metric.Bundles.ProtoMetric._.EqC.trans
d_trans_104 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_104 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
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
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v3)))))
-- Function.Metric.Bundles.ProtoMetric._.Eq.refl
d_refl_110 :: T_ProtoMetric_16 -> AgdaAny -> AgdaAny
d_refl_110 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
-- Function.Metric.Bundles.ProtoMetric._.Eq.sym
d_sym_114 ::
  T_ProtoMetric_16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_114 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe d_isProtoMetric_58 (coe v0)))))
-- Function.Metric.Bundles.ProtoMetric._.Eq.trans
d_trans_116 ::
  T_ProtoMetric_16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_116 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe d_isProtoMetric_58 (coe v0)))))
-- Function.Metric.Bundles.PreMetric
d_PreMetric_128 a0 a1 a2 a3 a4 = ()
data T_PreMetric_128
  = C_PreMetric'46'constructor_4373 AgdaAny
                                    (AgdaAny -> AgdaAny -> AgdaAny)
                                    MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
-- Function.Metric.Bundles.PreMetric.Carrier
d_Carrier_156 :: T_PreMetric_128 -> ()
d_Carrier_156 = erased
-- Function.Metric.Bundles.PreMetric.Image
d_Image_158 :: T_PreMetric_128 -> ()
d_Image_158 = erased
-- Function.Metric.Bundles.PreMetric._≈_
d__'8776'__160 :: T_PreMetric_128 -> AgdaAny -> AgdaAny -> ()
d__'8776'__160 = erased
-- Function.Metric.Bundles.PreMetric._≈ᵢ_
d__'8776''7522'__162 :: T_PreMetric_128 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__162 = erased
-- Function.Metric.Bundles.PreMetric._≤_
d__'8804'__164 :: T_PreMetric_128 -> AgdaAny -> AgdaAny -> ()
d__'8804'__164 = erased
-- Function.Metric.Bundles.PreMetric.0#
d_0'35'_166 :: T_PreMetric_128 -> AgdaAny
d_0'35'_166 v0
  = case coe v0 of
      C_PreMetric'46'constructor_4373 v6 v7 v8 -> coe v6
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.PreMetric.d
d_d_168 :: T_PreMetric_128 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_168 v0
  = case coe v0 of
      C_PreMetric'46'constructor_4373 v6 v7 v8 -> coe v7
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.PreMetric.isPreMetric
d_isPreMetric_170 ::
  T_PreMetric_128 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_170 v0
  = case coe v0 of
      C_PreMetric'46'constructor_4373 v6 v7 v8 -> coe v8
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.PreMetric._.antisym
d_antisym_174 ::
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_174 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_170 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.cong
d_cong_176 ::
  T_PreMetric_128 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_176 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_170 (coe v0)))
-- Function.Metric.Bundles.PreMetric._.isEquivalence
d_isEquivalence_178 ::
  T_PreMetric_128 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe d_isPreMetric_170 (coe v0)))))
-- Function.Metric.Bundles.PreMetric._.isPartialOrder
d_isPartialOrder_180 ::
  T_PreMetric_128 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_180 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_170 (coe v0)))
-- Function.Metric.Bundles.PreMetric._.isPreorder
d_isPreorder_182 ::
  T_PreMetric_128 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_182 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_170 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.isProtoMetric
d_isProtoMetric_184 ::
  T_PreMetric_128 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_184 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe d_isPreMetric_170 (coe v0))
-- Function.Metric.Bundles.PreMetric._.nonNegative
d_nonNegative_186 ::
  T_PreMetric_128 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_186 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_170 (coe v0)))
-- Function.Metric.Bundles.PreMetric._.refl
d_refl_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 -> AgdaAny -> AgdaAny
d_refl_188 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_188 v5
du_refl_188 :: T_PreMetric_128 -> AgdaAny -> AgdaAny
du_refl_188 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.reflexive
d_reflexive_190 ::
  T_PreMetric_128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_190 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe d_isPreMetric_170 (coe v0)))))
-- Function.Metric.Bundles.PreMetric._.trans
d_trans_192 ::
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe d_isPreMetric_170 (coe v0)))))
-- Function.Metric.Bundles.PreMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_194 ::
  T_PreMetric_128 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_194 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_170 (coe v0)))
-- Function.Metric.Bundles.PreMetric._.≈⇒0
d_'8776''8658'0_196 ::
  T_PreMetric_128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_196 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''8658'0_112
      (coe d_isPreMetric_170 (coe v0))
-- Function.Metric.Bundles.PreMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_198 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_198 v5
du_'8764''45'resp'45''8776'_198 ::
  T_PreMetric_128 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_198 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_200 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_200 v5
du_'8764''45'resp'691''45''8776'_200 ::
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_200 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_202 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_202 v5
du_'8764''45'resp'737''45''8776'_202 ::
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_202 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_204 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_204 v5
du_'8818''45'resp'45''8776'_204 ::
  T_PreMetric_128 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_204 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_206 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_206 v5
du_'8818''45'resp'691''45''8776'_206 ::
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_206 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_208 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_208 v5
du_'8818''45'resp'737''45''8776'_208 ::
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_208 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Function.Metric.Bundles.PreMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_212 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_212 v5
du_isPartialEquivalence_212 ::
  T_PreMetric_128 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_212 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
               (coe v2))))
-- Function.Metric.Bundles.PreMetric._.EqC.refl
d_refl_214 :: T_PreMetric_128 -> AgdaAny -> AgdaAny
d_refl_214 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_170 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.EqC.reflexive
d_reflexive_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_216 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_216 v5
du_reflexive_216 ::
  T_PreMetric_128 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_216 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                 (coe v2))
              v3))
-- Function.Metric.Bundles.PreMetric._.EqC.sym
d_sym_218 ::
  T_PreMetric_128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_218 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_170 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.EqC.trans
d_trans_220 ::
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_220 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_170 (coe v0))))
-- Function.Metric.Bundles.PreMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_224 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_224 v5
du_isPartialEquivalence_224 ::
  T_PreMetric_128 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_224 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
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
-- Function.Metric.Bundles.PreMetric._.Eq.refl
d_refl_226 :: T_PreMetric_128 -> AgdaAny -> AgdaAny
d_refl_226 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe d_isPreMetric_170 (coe v0))))))
-- Function.Metric.Bundles.PreMetric._.Eq.reflexive
d_reflexive_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_228 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_228 v5
du_reflexive_228 ::
  T_PreMetric_128 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_228 v0
  = let v1 = d_isPreMetric_170 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                    (coe v2) in
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
-- Function.Metric.Bundles.PreMetric._.Eq.sym
d_sym_230 ::
  T_PreMetric_128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_230 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe d_isPreMetric_170 (coe v0))))))
-- Function.Metric.Bundles.PreMetric._.Eq.trans
d_trans_232 ::
  T_PreMetric_128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe d_isPreMetric_170 (coe v0))))))
-- Function.Metric.Bundles.PreMetric.protoMetric
d_protoMetric_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_128 -> T_ProtoMetric_16
d_protoMetric_234 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_protoMetric_234 v5
du_protoMetric_234 :: T_PreMetric_128 -> T_ProtoMetric_16
du_protoMetric_234 v0
  = coe
      C_ProtoMetric'46'constructor_967 (d_0'35'_166 (coe v0))
      (d_d_168 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_170 (coe v0)))
-- Function.Metric.Bundles.QuasiSemiMetric
d_QuasiSemiMetric_246 a0 a1 a2 a3 a4 = ()
data T_QuasiSemiMetric_246
  = C_QuasiSemiMetric'46'constructor_8353 AgdaAny
                                          (AgdaAny -> AgdaAny -> AgdaAny)
                                          MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
-- Function.Metric.Bundles.QuasiSemiMetric.Carrier
d_Carrier_274 :: T_QuasiSemiMetric_246 -> ()
d_Carrier_274 = erased
-- Function.Metric.Bundles.QuasiSemiMetric.Image
d_Image_276 :: T_QuasiSemiMetric_246 -> ()
d_Image_276 = erased
-- Function.Metric.Bundles.QuasiSemiMetric._≈_
d__'8776'__278 :: T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> ()
d__'8776'__278 = erased
-- Function.Metric.Bundles.QuasiSemiMetric._≈ᵢ_
d__'8776''7522'__280 ::
  T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__280 = erased
-- Function.Metric.Bundles.QuasiSemiMetric._≤_
d__'8804'__282 :: T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> ()
d__'8804'__282 = erased
-- Function.Metric.Bundles.QuasiSemiMetric.0#
d_0'35'_284 :: T_QuasiSemiMetric_246 -> AgdaAny
d_0'35'_284 v0
  = case coe v0 of
      C_QuasiSemiMetric'46'constructor_8353 v6 v7 v8 -> coe v6
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.QuasiSemiMetric.d
d_d_286 :: T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_286 v0
  = case coe v0 of
      C_QuasiSemiMetric'46'constructor_8353 v6 v7 v8 -> coe v7
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.QuasiSemiMetric.isQuasiSemiMetric
d_isQuasiSemiMetric_288 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_288 v0
  = case coe v0 of
      C_QuasiSemiMetric'46'constructor_8353 v6 v7 v8 -> coe v8
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.QuasiSemiMetric._.0⇒≈
d_0'8658''8776'_292 ::
  T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_292 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_184
      (coe d_isQuasiSemiMetric_288 (coe v0))
-- Function.Metric.Bundles.QuasiSemiMetric._.antisym
d_antisym_294 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_294 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_288 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.cong
d_cong_296 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_296 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe d_isQuasiSemiMetric_288 (coe v0))))
-- Function.Metric.Bundles.QuasiSemiMetric._.isEquivalence
d_isEquivalence_298 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_298 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe d_isQuasiSemiMetric_288 (coe v0))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.isPartialOrder
d_isPartialOrder_300 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_300 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe d_isQuasiSemiMetric_288 (coe v0))))
-- Function.Metric.Bundles.QuasiSemiMetric._.isPreMetric
d_isPreMetric_302 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_302 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
      (coe d_isQuasiSemiMetric_288 (coe v0))
-- Function.Metric.Bundles.QuasiSemiMetric._.isPreorder
d_isPreorder_304 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_288 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.isProtoMetric
d_isProtoMetric_306 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_306 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe d_isQuasiSemiMetric_288 (coe v0)))
-- Function.Metric.Bundles.QuasiSemiMetric._.nonNegative
d_nonNegative_308 ::
  T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_308 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe d_isQuasiSemiMetric_288 (coe v0))))
-- Function.Metric.Bundles.QuasiSemiMetric._.refl
d_refl_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny
d_refl_310 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_310 v5
du_refl_310 :: T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny
du_refl_310 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.reflexive
d_reflexive_312 ::
  T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_312 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe d_isQuasiSemiMetric_288 (coe v0))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.trans
d_trans_314 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_314 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe d_isQuasiSemiMetric_288 (coe v0))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_316 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_316 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe d_isQuasiSemiMetric_288 (coe v0))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≈⇒0
d_'8776''8658'0_318 ::
  T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_318 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''8658'0_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe d_isQuasiSemiMetric_288 (coe v0)))
-- Function.Metric.Bundles.QuasiSemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_320 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_320 v5
du_'8764''45'resp'45''8776'_320 ::
  T_QuasiSemiMetric_246 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_320 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_322 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_322 v5
du_'8764''45'resp'691''45''8776'_322 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_322 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_324 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_324 v5
du_'8764''45'resp'737''45''8776'_324 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_324 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_326 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_326 v5
du_'8818''45'resp'45''8776'_326 ::
  T_QuasiSemiMetric_246 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_326 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_328 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_328 v5
du_'8818''45'resp'691''45''8776'_328 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_328 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_330 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_330 v5
du_'8818''45'resp'737''45''8776'_330 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_330 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_334 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_334 v5
du_isPartialEquivalence_334 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_334 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                  (coe v3)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.refl
d_refl_336 :: T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny
d_refl_336 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_288 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.reflexive
d_reflexive_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_338 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_338 v5
du_reflexive_338 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_338 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                    (coe v3))
                 v4)))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.sym
d_sym_340 ::
  T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_340 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_288 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.EqC.trans
d_trans_342 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_342 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_288 (coe v0)))))
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_346 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_346 v5
du_isPartialEquivalence_346 ::
  T_QuasiSemiMetric_246 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_346 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
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
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.refl
d_refl_348 :: T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny
d_refl_348 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe d_isQuasiSemiMetric_288 (coe v0)))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.reflexive
d_reflexive_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_350 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_350 v5
du_reflexive_350 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_350 v0
  = let v1 = d_isQuasiSemiMetric_288 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                       (coe v3) in
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
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.sym
d_sym_352 ::
  T_QuasiSemiMetric_246 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_352 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe d_isQuasiSemiMetric_288 (coe v0)))))))
-- Function.Metric.Bundles.QuasiSemiMetric._.Eq.trans
d_trans_354 ::
  T_QuasiSemiMetric_246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_354 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe d_isQuasiSemiMetric_288 (coe v0)))))))
-- Function.Metric.Bundles.QuasiSemiMetric.preMetric
d_preMetric_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 -> T_PreMetric_128
d_preMetric_356 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_preMetric_356 v5
du_preMetric_356 :: T_QuasiSemiMetric_246 -> T_PreMetric_128
du_preMetric_356 v0
  = coe
      C_PreMetric'46'constructor_4373 (d_0'35'_284 (coe v0))
      (d_d_286 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe d_isQuasiSemiMetric_288 (coe v0)))
-- Function.Metric.Bundles.QuasiSemiMetric._.protoMetric
d_protoMetric_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_246 -> T_ProtoMetric_16
d_protoMetric_360 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_protoMetric_360 v5
du_protoMetric_360 :: T_QuasiSemiMetric_246 -> T_ProtoMetric_16
du_protoMetric_360 v0
  = coe du_protoMetric_234 (coe du_preMetric_356 (coe v0))
-- Function.Metric.Bundles.SemiMetric
d_SemiMetric_372 a0 a1 a2 a3 a4 = ()
data T_SemiMetric_372
  = C_SemiMetric'46'constructor_12653 AgdaAny
                                      (AgdaAny -> AgdaAny -> AgdaAny)
                                      MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_250
-- Function.Metric.Bundles.SemiMetric.Carrier
d_Carrier_400 :: T_SemiMetric_372 -> ()
d_Carrier_400 = erased
-- Function.Metric.Bundles.SemiMetric.Image
d_Image_402 :: T_SemiMetric_372 -> ()
d_Image_402 = erased
-- Function.Metric.Bundles.SemiMetric._≈_
d__'8776'__404 :: T_SemiMetric_372 -> AgdaAny -> AgdaAny -> ()
d__'8776'__404 = erased
-- Function.Metric.Bundles.SemiMetric._≈ᵢ_
d__'8776''7522'__406 ::
  T_SemiMetric_372 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__406 = erased
-- Function.Metric.Bundles.SemiMetric._≤_
d__'8804'__408 :: T_SemiMetric_372 -> AgdaAny -> AgdaAny -> ()
d__'8804'__408 = erased
-- Function.Metric.Bundles.SemiMetric.0#
d_0'35'_410 :: T_SemiMetric_372 -> AgdaAny
d_0'35'_410 v0
  = case coe v0 of
      C_SemiMetric'46'constructor_12653 v6 v7 v8 -> coe v6
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.SemiMetric.d
d_d_412 :: T_SemiMetric_372 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_412 v0
  = case coe v0 of
      C_SemiMetric'46'constructor_12653 v6 v7 v8 -> coe v7
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.SemiMetric.isSemiMetric
d_isSemiMetric_414 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_250
d_isSemiMetric_414 v0
  = case coe v0 of
      C_SemiMetric'46'constructor_12653 v6 v7 v8 -> coe v8
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.SemiMetric._.0⇒≈
d_0'8658''8776'_418 ::
  T_SemiMetric_372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_418 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe d_isSemiMetric_414 (coe v0)))
-- Function.Metric.Bundles.SemiMetric._.antisym
d_antisym_420 ::
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_420 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe d_isSemiMetric_414 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.cong
d_cong_422 ::
  T_SemiMetric_372 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_422 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe d_isSemiMetric_414 (coe v0)))))
-- Function.Metric.Bundles.SemiMetric._.isEquivalence
d_isEquivalence_424 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_424 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                     (coe d_isSemiMetric_414 (coe v0)))))))
-- Function.Metric.Bundles.SemiMetric._.isPartialOrder
d_isPartialOrder_426 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_426 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe d_isSemiMetric_414 (coe v0)))))
-- Function.Metric.Bundles.SemiMetric._.isPreMetric
d_isPreMetric_428 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_428 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe d_isSemiMetric_414 (coe v0)))
-- Function.Metric.Bundles.SemiMetric._.isPreorder
d_isPreorder_430 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_430 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe d_isSemiMetric_414 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.isProtoMetric
d_isProtoMetric_432 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_432 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
            (coe d_isSemiMetric_414 (coe v0))))
-- Function.Metric.Bundles.SemiMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_434 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_434 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
      (coe d_isSemiMetric_414 (coe v0))
-- Function.Metric.Bundles.SemiMetric._.nonNegative
d_nonNegative_436 ::
  T_SemiMetric_372 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_436 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe d_isSemiMetric_414 (coe v0)))))
-- Function.Metric.Bundles.SemiMetric._.refl
d_refl_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 -> AgdaAny -> AgdaAny
d_refl_438 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_438 v5
du_refl_438 :: T_SemiMetric_372 -> AgdaAny -> AgdaAny
du_refl_438 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.reflexive
d_reflexive_440 ::
  T_SemiMetric_372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_440 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                     (coe d_isSemiMetric_414 (coe v0)))))))
-- Function.Metric.Bundles.SemiMetric._.sym
d_sym_442 :: T_SemiMetric_372 -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_442 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_sym_260
      (coe d_isSemiMetric_414 (coe v0))
-- Function.Metric.Bundles.SemiMetric._.trans
d_trans_444 ::
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_444 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                     (coe d_isSemiMetric_414 (coe v0)))))))
-- Function.Metric.Bundles.SemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_446 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_446 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe d_isSemiMetric_414 (coe v0)))))
-- Function.Metric.Bundles.SemiMetric._.≈⇒0
d_'8776''8658'0_448 ::
  T_SemiMetric_372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_448 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''8658'0_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
            (coe d_isSemiMetric_414 (coe v0))))
-- Function.Metric.Bundles.SemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_450 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_450 v5
du_'8764''45'resp'45''8776'_450 ::
  T_SemiMetric_372 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_450 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_452 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_452 v5
du_'8764''45'resp'691''45''8776'_452 ::
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_452 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_454 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_454 v5
du_'8764''45'resp'737''45''8776'_454 ::
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_454 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_456 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_456 v5
du_'8818''45'resp'45''8776'_456 ::
  T_SemiMetric_372 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_456 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_458 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_458 v5
du_'8818''45'resp'691''45''8776'_458 ::
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_458 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_460 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_460 v5
du_'8818''45'resp'737''45''8776'_460 ::
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_460 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Function.Metric.Bundles.SemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_464 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_464 v5
du_isPartialEquivalence_464 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_464 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                     (coe v4))))))
-- Function.Metric.Bundles.SemiMetric._.EqC.refl
d_refl_466 :: T_SemiMetric_372 -> AgdaAny -> AgdaAny
d_refl_466 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe d_isSemiMetric_414 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.EqC.reflexive
d_reflexive_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_468 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_468 v5
du_reflexive_468 ::
  T_SemiMetric_372 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_468 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe
                       MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                       (coe v4))
                    v5))))
-- Function.Metric.Bundles.SemiMetric._.EqC.sym
d_sym_470 ::
  T_SemiMetric_372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_470 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe d_isSemiMetric_414 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.EqC.trans
d_trans_472 ::
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_472 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe d_isSemiMetric_414 (coe v0))))))
-- Function.Metric.Bundles.SemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_476 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_476 v5
du_isPartialEquivalence_476 ::
  T_SemiMetric_372 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_476 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
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
-- Function.Metric.Bundles.SemiMetric._.Eq.refl
d_refl_478 :: T_SemiMetric_372 -> AgdaAny -> AgdaAny
d_refl_478 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                        (coe d_isSemiMetric_414 (coe v0))))))))
-- Function.Metric.Bundles.SemiMetric._.Eq.reflexive
d_reflexive_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_480 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_480 v5
du_reflexive_480 ::
  T_SemiMetric_372 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_480 v0
  = let v1 = d_isSemiMetric_414 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                          (coe v4) in
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
-- Function.Metric.Bundles.SemiMetric._.Eq.sym
d_sym_482 ::
  T_SemiMetric_372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_482 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                        (coe d_isSemiMetric_414 (coe v0))))))))
-- Function.Metric.Bundles.SemiMetric._.Eq.trans
d_trans_484 ::
  T_SemiMetric_372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_484 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                        (coe d_isSemiMetric_414 (coe v0))))))))
-- Function.Metric.Bundles.SemiMetric.quasiSemiMetric
d_quasiSemiMetric_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 -> T_QuasiSemiMetric_246
d_quasiSemiMetric_486 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_quasiSemiMetric_486 v5
du_quasiSemiMetric_486 :: T_SemiMetric_372 -> T_QuasiSemiMetric_246
du_quasiSemiMetric_486 v0
  = coe
      C_QuasiSemiMetric'46'constructor_8353 (d_0'35'_410 (coe v0))
      (d_d_412 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe d_isSemiMetric_414 (coe v0)))
-- Function.Metric.Bundles.SemiMetric._.preMetric
d_preMetric_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 -> T_PreMetric_128
d_preMetric_490 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_preMetric_490 v5
du_preMetric_490 :: T_SemiMetric_372 -> T_PreMetric_128
du_preMetric_490 v0
  = coe du_preMetric_356 (coe du_quasiSemiMetric_486 (coe v0))
-- Function.Metric.Bundles.SemiMetric._.protoMetric
d_protoMetric_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_372 -> T_ProtoMetric_16
d_protoMetric_492 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_protoMetric_492 v5
du_protoMetric_492 :: T_SemiMetric_372 -> T_ProtoMetric_16
du_protoMetric_492 v0
  = let v1 = coe du_quasiSemiMetric_486 (coe v0) in
    coe (coe du_protoMetric_234 (coe du_preMetric_356 (coe v1)))
-- Function.Metric.Bundles.GeneralMetric
d_GeneralMetric_504 a0 a1 a2 a3 a4 = ()
data T_GeneralMetric_504
  = C_GeneralMetric'46'constructor_17243 AgdaAny
                                         (AgdaAny -> AgdaAny -> AgdaAny)
                                         (AgdaAny -> AgdaAny -> AgdaAny)
                                         MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_332
-- Function.Metric.Bundles.GeneralMetric.Carrier
d_Carrier_534 :: T_GeneralMetric_504 -> ()
d_Carrier_534 = erased
-- Function.Metric.Bundles.GeneralMetric.Image
d_Image_536 :: T_GeneralMetric_504 -> ()
d_Image_536 = erased
-- Function.Metric.Bundles.GeneralMetric._≈_
d__'8776'__538 :: T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> ()
d__'8776'__538 = erased
-- Function.Metric.Bundles.GeneralMetric._≈ᵢ_
d__'8776''7522'__540 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> ()
d__'8776''7522'__540 = erased
-- Function.Metric.Bundles.GeneralMetric._≤_
d__'8804'__542 :: T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> ()
d__'8804'__542 = erased
-- Function.Metric.Bundles.GeneralMetric.0#
d_0'35'_544 :: T_GeneralMetric_504 -> AgdaAny
d_0'35'_544 v0
  = case coe v0 of
      C_GeneralMetric'46'constructor_17243 v6 v7 v8 v9 -> coe v6
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.GeneralMetric._∙_
d__'8729'__546 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__546 v0
  = case coe v0 of
      C_GeneralMetric'46'constructor_17243 v6 v7 v8 v9 -> coe v7
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.GeneralMetric.d
d_d_548 :: T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny
d_d_548 v0
  = case coe v0 of
      C_GeneralMetric'46'constructor_17243 v6 v7 v8 v9 -> coe v8
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.GeneralMetric.isGeneralMetric
d_isGeneralMetric_550 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_332
d_isGeneralMetric_550 v0
  = case coe v0 of
      C_GeneralMetric'46'constructor_17243 v6 v7 v8 v9 -> coe v9
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Bundles.GeneralMetric._.0⇒≈
d_0'8658''8776'_554 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_0'8658''8776'_554 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
            (coe d_isGeneralMetric_550 (coe v0))))
-- Function.Metric.Bundles.GeneralMetric._.antisym
d_antisym_556 ::
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_556 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                     (coe d_isGeneralMetric_550 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.cong
d_cong_558 ::
  T_GeneralMetric_504 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_558 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_cong_46
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                  (coe d_isGeneralMetric_550 (coe v0))))))
-- Function.Metric.Bundles.GeneralMetric._.isEquivalence
d_isEquivalence_560 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_560 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                        (coe d_isGeneralMetric_550 (coe v0))))))))
-- Function.Metric.Bundles.GeneralMetric._.isPartialOrder
d_isPartialOrder_562 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_562 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                  (coe d_isGeneralMetric_550 (coe v0))))))
-- Function.Metric.Bundles.GeneralMetric._.isPreMetric
d_isPreMetric_564 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_564 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
            (coe d_isGeneralMetric_550 (coe v0))))
-- Function.Metric.Bundles.GeneralMetric._.isPreorder
d_isPreorder_566 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_566 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                     (coe d_isGeneralMetric_550 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.isProtoMetric
d_isProtoMetric_568 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_568 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
               (coe d_isGeneralMetric_550 (coe v0)))))
-- Function.Metric.Bundles.GeneralMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_570 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_570 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
         (coe d_isGeneralMetric_550 (coe v0)))
-- Function.Metric.Bundles.GeneralMetric._.isSemiMetric
d_isSemiMetric_572 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_250
d_isSemiMetric_572 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
      (coe d_isGeneralMetric_550 (coe v0))
-- Function.Metric.Bundles.GeneralMetric._.nonNegative
d_nonNegative_574 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny
d_nonNegative_574 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                  (coe d_isGeneralMetric_550 (coe v0))))))
-- Function.Metric.Bundles.GeneralMetric._.refl
d_refl_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny
d_refl_576 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_576 v5
du_refl_576 :: T_GeneralMetric_504 -> AgdaAny -> AgdaAny
du_refl_576 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.reflexive
d_reflexive_578 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_578 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                        (coe d_isGeneralMetric_550 (coe v0))))))))
-- Function.Metric.Bundles.GeneralMetric._.sym
d_sym_580 :: T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_580 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_sym_260
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
         (coe d_isGeneralMetric_550 (coe v0)))
-- Function.Metric.Bundles.GeneralMetric._.trans
d_trans_582 ::
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_582 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                        (coe d_isGeneralMetric_550 (coe v0))))))))
-- Function.Metric.Bundles.GeneralMetric._.triangle
d_triangle_584 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_triangle_584 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_triangle_344
      (coe d_isGeneralMetric_550 (coe v0))
-- Function.Metric.Bundles.GeneralMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_586 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_586 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                  (coe d_isGeneralMetric_550 (coe v0))))))
-- Function.Metric.Bundles.GeneralMetric._.≈⇒0
d_'8776''8658'0_588 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8776''8658'0_588 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''8658'0_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
               (coe d_isGeneralMetric_550 (coe v0)))))
-- Function.Metric.Bundles.GeneralMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_590 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_590 v5
du_'8764''45'resp'45''8776'_590 ::
  T_GeneralMetric_504 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_590 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_592 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_592 v5
du_'8764''45'resp'691''45''8776'_592 ::
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_592 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_594 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_594 v5
du_'8764''45'resp'737''45''8776'_594 ::
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_594 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_596 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_596 v5
du_'8818''45'resp'45''8776'_596 ::
  T_GeneralMetric_504 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_596 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_598 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_598 v5
du_'8818''45'resp'691''45''8776'_598 ::
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_598 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_600 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_600 v5
du_'8818''45'resp'737''45''8776'_600 ::
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_600 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                           (coe v6))))))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_604 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_604 v5
du_isPartialEquivalence_604 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_604 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                        (coe v5)))))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.refl
d_refl_606 :: T_GeneralMetric_504 -> AgdaAny -> AgdaAny
d_refl_606 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                     (coe d_isGeneralMetric_550 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.reflexive
d_reflexive_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_608 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_608 v5
du_reflexive_608 ::
  T_GeneralMetric_504 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_608 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe
                          MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
                          (coe v5))
                       v6)))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.sym
d_sym_610 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_610 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                     (coe d_isGeneralMetric_550 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.EqC.trans
d_trans_612 ::
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_612 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                     (coe d_isGeneralMetric_550 (coe v0)))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_616 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_616 v5
du_isPartialEquivalence_616 ::
  T_GeneralMetric_504 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_616 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                                (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                              (coe v7)))))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.refl
d_refl_618 :: T_GeneralMetric_504 -> AgdaAny -> AgdaAny
d_refl_618 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                        (coe
                           MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                           (coe d_isGeneralMetric_550 (coe v0)))))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.reflexive
d_reflexive_620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_620 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_620 v5
du_reflexive_620 ::
  T_GeneralMetric_504 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_620 v0
  = let v1 = d_isGeneralMetric_550 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
                             (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                                (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                                (coe v7))
                             v8)))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.sym
d_sym_622 ::
  T_GeneralMetric_504 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_622 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                        (coe
                           MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                           (coe d_isGeneralMetric_550 (coe v0)))))))))
-- Function.Metric.Bundles.GeneralMetric._.Eq.trans
d_trans_624 ::
  T_GeneralMetric_504 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_624 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
                     (coe
                        MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
                        (coe
                           MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
                           (coe d_isGeneralMetric_550 (coe v0)))))))))
-- Function.Metric.Bundles.GeneralMetric.semiMetric
d_semiMetric_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 -> T_SemiMetric_372
d_semiMetric_626 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_semiMetric_626 v5
du_semiMetric_626 :: T_GeneralMetric_504 -> T_SemiMetric_372
du_semiMetric_626 v0
  = coe
      C_SemiMetric'46'constructor_12653 (d_0'35'_544 (coe v0))
      (d_d_548 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
         (coe d_isGeneralMetric_550 (coe v0)))
-- Function.Metric.Bundles.GeneralMetric._.preMetric
d_preMetric_630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 -> T_PreMetric_128
d_preMetric_630 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_preMetric_630 v5
du_preMetric_630 :: T_GeneralMetric_504 -> T_PreMetric_128
du_preMetric_630 v0
  = let v1 = coe du_semiMetric_626 (coe v0) in
    coe (coe du_preMetric_356 (coe du_quasiSemiMetric_486 (coe v1)))
-- Function.Metric.Bundles.GeneralMetric._.protoMetric
d_protoMetric_632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 -> T_ProtoMetric_16
d_protoMetric_632 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_protoMetric_632 v5
du_protoMetric_632 :: T_GeneralMetric_504 -> T_ProtoMetric_16
du_protoMetric_632 v0
  = let v1 = coe du_semiMetric_626 (coe v0) in
    coe
      (let v2 = coe du_quasiSemiMetric_486 (coe v1) in
       coe (coe du_protoMetric_234 (coe du_preMetric_356 (coe v2))))
-- Function.Metric.Bundles.GeneralMetric._.quasiSemiMetric
d_quasiSemiMetric_634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_GeneralMetric_504 -> T_QuasiSemiMetric_246
d_quasiSemiMetric_634 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_quasiSemiMetric_634 v5
du_quasiSemiMetric_634 ::
  T_GeneralMetric_504 -> T_QuasiSemiMetric_246
du_quasiSemiMetric_634 v0
  = coe du_quasiSemiMetric_486 (coe du_semiMetric_626 (coe v0))
