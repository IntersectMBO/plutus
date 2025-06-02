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

module MAlonzo.Code.Function.Metric.Nat.Bundles where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Nat.Base qualified
import MAlonzo.Code.Function.Metric.Structures qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Metric.Nat.Bundles.ProtoMetric
d_ProtoMetric_12 a0 a1 = ()
data T_ProtoMetric_12
  = C_ProtoMetric'46'constructor_193 (AgdaAny -> AgdaAny -> Integer)
                                     MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
-- Function.Metric.Nat.Bundles.ProtoMetric.Carrier
d_Carrier_26 :: T_ProtoMetric_12 -> ()
d_Carrier_26 = erased
-- Function.Metric.Nat.Bundles.ProtoMetric._≈_
d__'8776'__28 :: T_ProtoMetric_12 -> AgdaAny -> AgdaAny -> ()
d__'8776'__28 = erased
-- Function.Metric.Nat.Bundles.ProtoMetric.d
d_d_30 :: T_ProtoMetric_12 -> AgdaAny -> AgdaAny -> Integer
d_d_30 v0
  = case coe v0 of
      C_ProtoMetric'46'constructor_193 v3 v4 -> coe v3
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.ProtoMetric.isProtoMetric
d_isProtoMetric_32 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_32 v0
  = case coe v0 of
      C_ProtoMetric'46'constructor_193 v3 v4 -> coe v4
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.ProtoMetric._.antisym
d_antisym_36 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_36 = erased
-- Function.Metric.Nat.Bundles.ProtoMetric._.cong
d_cong_38 ::
  T_ProtoMetric_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_38 = erased
-- Function.Metric.Nat.Bundles.ProtoMetric._.isEquivalence
d_isEquivalence_40 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_40 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_32 (coe v0))))
-- Function.Metric.Nat.Bundles.ProtoMetric._.isPartialOrder
d_isPartialOrder_42 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_42 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe d_isProtoMetric_32 (coe v0))
-- Function.Metric.Nat.Bundles.ProtoMetric._.isPreorder
d_isPreorder_44 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_44 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe d_isProtoMetric_32 (coe v0)))
-- Function.Metric.Nat.Bundles.ProtoMetric._.nonNegative
d_nonNegative_46 ::
  T_ProtoMetric_12 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_46 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe d_isProtoMetric_32 (coe v0))
-- Function.Metric.Nat.Bundles.ProtoMetric._.refl
d_refl_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_48 ~v0 ~v1 v2 = du_refl_48 v2
du_refl_48 ::
  T_ProtoMetric_12 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_48 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
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
-- Function.Metric.Nat.Bundles.ProtoMetric._.reflexive
d_reflexive_50 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_50 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_32 (coe v0))))
-- Function.Metric.Nat.Bundles.ProtoMetric._.trans
d_trans_52 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_52 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_32 (coe v0))))
-- Function.Metric.Nat.Bundles.ProtoMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_54 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_54 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe d_isProtoMetric_32 (coe v0))
-- Function.Metric.Nat.Bundles.ProtoMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_56 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_56 v2
du_'8764''45'resp'45''8776'_56 ::
  T_ProtoMetric_12 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_56 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
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
-- Function.Metric.Nat.Bundles.ProtoMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_58 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_58 v2
du_'8764''45'resp'691''45''8776'_58 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_58 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
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
-- Function.Metric.Nat.Bundles.ProtoMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_60 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_60 v2
du_'8764''45'resp'737''45''8776'_60 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_60 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
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
-- Function.Metric.Nat.Bundles.ProtoMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_62 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_62 v2
du_'8818''45'resp'45''8776'_62 ::
  T_ProtoMetric_12 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_62 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
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
-- Function.Metric.Nat.Bundles.ProtoMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_64 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_64 v2
du_'8818''45'resp'691''45''8776'_64 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_64 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
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
-- Function.Metric.Nat.Bundles.ProtoMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_66 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_66 v2
du_'8818''45'resp'737''45''8776'_66 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_66 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
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
-- Function.Metric.Nat.Bundles.ProtoMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_70 ~v0 ~v1 v2
  = du_isPartialEquivalence_70 v2
du_isPartialEquivalence_70 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_70 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
            (coe v1)))
-- Function.Metric.Nat.Bundles.ProtoMetric._.EqC.refl
d_refl_72 :: T_ProtoMetric_12 -> AgdaAny -> AgdaAny
d_refl_72 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_32 (coe v0)))
-- Function.Metric.Nat.Bundles.ProtoMetric._.EqC.reflexive
d_reflexive_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_74 ~v0 ~v1 v2 = du_reflexive_74 v2
du_reflexive_74 ::
  T_ProtoMetric_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_74 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
              (coe v1))
           v2)
-- Function.Metric.Nat.Bundles.ProtoMetric._.EqC.sym
d_sym_76 ::
  T_ProtoMetric_12 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_76 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_32 (coe v0)))
-- Function.Metric.Nat.Bundles.ProtoMetric._.EqC.trans
d_trans_78 ::
  T_ProtoMetric_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_32 (coe v0)))
-- Function.Metric.Nat.Bundles.ProtoMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_82 ~v0 ~v1 v2
  = du_isPartialEquivalence_82 v2
du_isPartialEquivalence_82 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_82 v0
  = let v1 = d_isProtoMetric_32 (coe v0) in
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
-- Function.Metric.Nat.Bundles.ProtoMetric._.Eq.refl
d_refl_84 ::
  T_ProtoMetric_12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_84 = erased
-- Function.Metric.Nat.Bundles.ProtoMetric._.Eq.reflexive
d_reflexive_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_86 = erased
-- Function.Metric.Nat.Bundles.ProtoMetric._.Eq.sym
d_sym_88 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_88 = erased
-- Function.Metric.Nat.Bundles.ProtoMetric._.Eq.trans
d_trans_90 ::
  T_ProtoMetric_12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_90 = erased
-- Function.Metric.Nat.Bundles.PreMetric
d_PreMetric_96 a0 a1 = ()
data T_PreMetric_96
  = C_PreMetric'46'constructor_1629 (AgdaAny -> AgdaAny -> Integer)
                                    MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
-- Function.Metric.Nat.Bundles.PreMetric.Carrier
d_Carrier_110 :: T_PreMetric_96 -> ()
d_Carrier_110 = erased
-- Function.Metric.Nat.Bundles.PreMetric._≈_
d__'8776'__112 :: T_PreMetric_96 -> AgdaAny -> AgdaAny -> ()
d__'8776'__112 = erased
-- Function.Metric.Nat.Bundles.PreMetric.d
d_d_114 :: T_PreMetric_96 -> AgdaAny -> AgdaAny -> Integer
d_d_114 v0
  = case coe v0 of
      C_PreMetric'46'constructor_1629 v3 v4 -> coe v3
      _                                     -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.PreMetric.isPreMetric
d_isPreMetric_116 ::
  T_PreMetric_96 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_116 v0
  = case coe v0 of
      C_PreMetric'46'constructor_1629 v3 v4 -> coe v4
      _                                     -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.PreMetric._.antisym
d_antisym_120 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_120 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.cong
d_cong_122 ::
  T_PreMetric_96 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_122 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.isEquivalence
d_isEquivalence_124 ::
  T_PreMetric_96 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_124 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe d_isPreMetric_116 (coe v0)))))
-- Function.Metric.Nat.Bundles.PreMetric._.isPartialOrder
d_isPartialOrder_126 ::
  T_PreMetric_96 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_126 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_116 (coe v0)))
-- Function.Metric.Nat.Bundles.PreMetric._.isPreorder
d_isPreorder_128 ::
  T_PreMetric_96 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_128 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_116 (coe v0))))
-- Function.Metric.Nat.Bundles.PreMetric._.isProtoMetric
d_isProtoMetric_130 ::
  T_PreMetric_96 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_130 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe d_isPreMetric_116 (coe v0))
-- Function.Metric.Nat.Bundles.PreMetric._.nonNegative
d_nonNegative_132 ::
  T_PreMetric_96 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_132 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_116 (coe v0)))
-- Function.Metric.Nat.Bundles.PreMetric._.refl
d_refl_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_134 ~v0 ~v1 v2 = du_refl_134 v2
du_refl_134 ::
  T_PreMetric_96 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_134 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.reflexive
d_reflexive_136 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_136 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe d_isPreMetric_116 (coe v0)))))
-- Function.Metric.Nat.Bundles.PreMetric._.trans
d_trans_138 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_138 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
               (coe d_isPreMetric_116 (coe v0)))))
-- Function.Metric.Nat.Bundles.PreMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_140 ::
  T_PreMetric_96 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_140 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_116 (coe v0)))
-- Function.Metric.Nat.Bundles.PreMetric._.≈⇒0
d_'8776''8658'0_142 ::
  T_PreMetric_96 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_142 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_144 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_144 v2
du_'8764''45'resp'45''8776'_144 ::
  T_PreMetric_96 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_144 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_146 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_146 v2
du_'8764''45'resp'691''45''8776'_146 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_146 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_148 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_148 v2
du_'8764''45'resp'737''45''8776'_148 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_148 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_150 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_150 v2
du_'8818''45'resp'45''8776'_150 ::
  T_PreMetric_96 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_150 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_152 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_152 v2
du_'8818''45'resp'691''45''8776'_152 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_152 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_154 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_154 v2
du_'8818''45'resp'737''45''8776'_154 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_154 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_158 ~v0 ~v1 v2
  = du_isPartialEquivalence_158 v2
du_isPartialEquivalence_158 ::
  T_PreMetric_96 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_158 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.refl
d_refl_160 :: T_PreMetric_96 -> AgdaAny -> AgdaAny
d_refl_160 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_116 (coe v0))))
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.reflexive
d_reflexive_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_162 ~v0 ~v1 v2 = du_reflexive_162 v2
du_reflexive_162 ::
  T_PreMetric_96 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_162 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.sym
d_sym_164 ::
  T_PreMetric_96 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_164 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_116 (coe v0))))
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.trans
d_trans_166 ::
  T_PreMetric_96 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe d_isPreMetric_116 (coe v0))))
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_170 ~v0 ~v1 v2
  = du_isPartialEquivalence_170 v2
du_isPartialEquivalence_170 ::
  T_PreMetric_96 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_170 v0
  = let v1 = d_isPreMetric_116 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.refl
d_refl_172 ::
  T_PreMetric_96 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_172 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.reflexive
d_reflexive_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_174 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.sym
d_sym_176 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_176 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.trans
d_trans_178 ::
  T_PreMetric_96 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_178 = erased
-- Function.Metric.Nat.Bundles.PreMetric.protoMetric
d_protoMetric_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_96 -> T_ProtoMetric_12
d_protoMetric_180 ~v0 ~v1 v2 = du_protoMetric_180 v2
du_protoMetric_180 :: T_PreMetric_96 -> T_ProtoMetric_12
du_protoMetric_180 v0
  = coe
      C_ProtoMetric'46'constructor_193 (d_d_114 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe d_isPreMetric_116 (coe v0)))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric
d_QuasiSemiMetric_186 a0 a1 = ()
data T_QuasiSemiMetric_186
  = C_QuasiSemiMetric'46'constructor_3255 (AgdaAny ->
                                           AgdaAny -> Integer)
                                          MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
-- Function.Metric.Nat.Bundles.QuasiSemiMetric.Carrier
d_Carrier_200 :: T_QuasiSemiMetric_186 -> ()
d_Carrier_200 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._≈_
d__'8776'__202 :: T_QuasiSemiMetric_186 -> AgdaAny -> AgdaAny -> ()
d__'8776'__202 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric.d
d_d_204 :: T_QuasiSemiMetric_186 -> AgdaAny -> AgdaAny -> Integer
d_d_204 v0
  = case coe v0 of
      C_QuasiSemiMetric'46'constructor_3255 v3 v4 -> coe v3
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.QuasiSemiMetric.isQuasiSemiMetric
d_isQuasiSemiMetric_206 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_206 v0
  = case coe v0 of
      C_QuasiSemiMetric'46'constructor_3255 v3 v4 -> coe v4
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.0⇒≈
d_0'8658''8776'_210 ::
  T_QuasiSemiMetric_186 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_210 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_184
      (coe d_isQuasiSemiMetric_206 (coe v0))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.antisym
d_antisym_212 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_212 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.cong
d_cong_214 ::
  T_QuasiSemiMetric_186 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_214 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isEquivalence
d_isEquivalence_216 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_216 v0
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
                  (coe d_isQuasiSemiMetric_206 (coe v0))))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isPartialOrder
d_isPartialOrder_218 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_218 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe d_isQuasiSemiMetric_206 (coe v0))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isPreMetric
d_isPreMetric_220 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_220 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
      (coe d_isQuasiSemiMetric_206 (coe v0))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isPreorder
d_isPreorder_222 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_222 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_206 (coe v0)))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isProtoMetric
d_isProtoMetric_224 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_224 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe d_isQuasiSemiMetric_206 (coe v0)))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.nonNegative
d_nonNegative_226 ::
  T_QuasiSemiMetric_186 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_226 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe d_isQuasiSemiMetric_206 (coe v0))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.refl
d_refl_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_228 ~v0 ~v1 v2 = du_refl_228 v2
du_refl_228 ::
  T_QuasiSemiMetric_186 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_228 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.reflexive
d_reflexive_230 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_230 v0
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
                  (coe d_isQuasiSemiMetric_206 (coe v0))))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.trans
d_trans_232 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_232 v0
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
                  (coe d_isQuasiSemiMetric_206 (coe v0))))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_234 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_234 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe d_isQuasiSemiMetric_206 (coe v0))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≈⇒0
d_'8776''8658'0_236 ::
  T_QuasiSemiMetric_186 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_236 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_238 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_238 v2
du_'8764''45'resp'45''8776'_238 ::
  T_QuasiSemiMetric_186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_238 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_240 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_240 v2
du_'8764''45'resp'691''45''8776'_240 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_240 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_242 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_242 v2
du_'8764''45'resp'737''45''8776'_242 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_242 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_244 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_244 v2
du_'8818''45'resp'45''8776'_244 ::
  T_QuasiSemiMetric_186 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_244 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_246 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_246 v2
du_'8818''45'resp'691''45''8776'_246 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_246 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_248 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_248 v2
du_'8818''45'resp'737''45''8776'_248 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_248 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_252 ~v0 ~v1 v2
  = du_isPartialEquivalence_252 v2
du_isPartialEquivalence_252 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_252 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.refl
d_refl_254 :: T_QuasiSemiMetric_186 -> AgdaAny -> AgdaAny
d_refl_254 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_206 (coe v0)))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.reflexive
d_reflexive_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_256 ~v0 ~v1 v2 = du_reflexive_256 v2
du_reflexive_256 ::
  T_QuasiSemiMetric_186 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_256 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.sym
d_sym_258 ::
  T_QuasiSemiMetric_186 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_258 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_206 (coe v0)))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.trans
d_trans_260 ::
  T_QuasiSemiMetric_186 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_260 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
               (coe d_isQuasiSemiMetric_206 (coe v0)))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_264 ~v0 ~v1 v2
  = du_isPartialEquivalence_264 v2
du_isPartialEquivalence_264 ::
  T_QuasiSemiMetric_186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_264 v0
  = let v1 = d_isQuasiSemiMetric_206 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.refl
d_refl_266 ::
  T_QuasiSemiMetric_186 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_266 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.reflexive
d_reflexive_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_268 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.sym
d_sym_270 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_270 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.trans
d_trans_272 ::
  T_QuasiSemiMetric_186 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_272 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric.preMetric
d_preMetric_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 -> T_PreMetric_96
d_preMetric_274 ~v0 ~v1 v2 = du_preMetric_274 v2
du_preMetric_274 :: T_QuasiSemiMetric_186 -> T_PreMetric_96
du_preMetric_274 v0
  = coe
      C_PreMetric'46'constructor_1629 (d_d_204 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe d_isQuasiSemiMetric_206 (coe v0)))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.protoMetric
d_protoMetric_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_186 -> T_ProtoMetric_12
d_protoMetric_278 ~v0 ~v1 v2 = du_protoMetric_278 v2
du_protoMetric_278 :: T_QuasiSemiMetric_186 -> T_ProtoMetric_12
du_protoMetric_278 v0
  = coe du_protoMetric_180 (coe du_preMetric_274 (coe v0))
-- Function.Metric.Nat.Bundles.SemiMetric
d_SemiMetric_284 a0 a1 = ()
data T_SemiMetric_284
  = C_SemiMetric'46'constructor_4991 (AgdaAny -> AgdaAny -> Integer)
                                     MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_250
-- Function.Metric.Nat.Bundles.SemiMetric.Carrier
d_Carrier_298 :: T_SemiMetric_284 -> ()
d_Carrier_298 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._≈_
d__'8776'__300 :: T_SemiMetric_284 -> AgdaAny -> AgdaAny -> ()
d__'8776'__300 = erased
-- Function.Metric.Nat.Bundles.SemiMetric.d
d_d_302 :: T_SemiMetric_284 -> AgdaAny -> AgdaAny -> Integer
d_d_302 v0
  = case coe v0 of
      C_SemiMetric'46'constructor_4991 v3 v4 -> coe v3
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.SemiMetric.isSemiMetric
d_isSemiMetric_304 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_250
d_isSemiMetric_304 v0
  = case coe v0 of
      C_SemiMetric'46'constructor_4991 v3 v4 -> coe v4
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.SemiMetric._.0⇒≈
d_0'8658''8776'_308 ::
  T_SemiMetric_284 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_308 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe d_isSemiMetric_304 (coe v0)))
-- Function.Metric.Nat.Bundles.SemiMetric._.antisym
d_antisym_310 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_310 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.cong
d_cong_312 ::
  T_SemiMetric_284 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_312 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.isEquivalence
d_isEquivalence_314 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_314 v0
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
                     (coe d_isSemiMetric_304 (coe v0)))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.isPartialOrder
d_isPartialOrder_316 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_316 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe d_isSemiMetric_304 (coe v0)))))
-- Function.Metric.Nat.Bundles.SemiMetric._.isPreMetric
d_isPreMetric_318 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_318 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe d_isSemiMetric_304 (coe v0)))
-- Function.Metric.Nat.Bundles.SemiMetric._.isPreorder
d_isPreorder_320 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_320 v0
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
                  (coe d_isSemiMetric_304 (coe v0))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.isProtoMetric
d_isProtoMetric_322 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_322 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
            (coe d_isSemiMetric_304 (coe v0))))
-- Function.Metric.Nat.Bundles.SemiMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_324 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_324 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
      (coe d_isSemiMetric_304 (coe v0))
-- Function.Metric.Nat.Bundles.SemiMetric._.nonNegative
d_nonNegative_326 ::
  T_SemiMetric_284 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_326 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe d_isSemiMetric_304 (coe v0)))))
-- Function.Metric.Nat.Bundles.SemiMetric._.refl
d_refl_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_328 ~v0 ~v1 v2 = du_refl_328 v2
du_refl_328 ::
  T_SemiMetric_284 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_328 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.reflexive
d_reflexive_330 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_330 v0
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
                     (coe d_isSemiMetric_304 (coe v0)))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.sym
d_sym_332 ::
  T_SemiMetric_284 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_332 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.trans
d_trans_334 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_334 v0
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
                     (coe d_isSemiMetric_304 (coe v0)))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_336 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_336 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
               (coe d_isSemiMetric_304 (coe v0)))))
-- Function.Metric.Nat.Bundles.SemiMetric._.≈⇒0
d_'8776''8658'0_338 ::
  T_SemiMetric_284 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_338 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_340 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_340 v2
du_'8764''45'resp'45''8776'_340 ::
  T_SemiMetric_284 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_340 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_342 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_342 v2
du_'8764''45'resp'691''45''8776'_342 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_342 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_344 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_344 v2
du_'8764''45'resp'737''45''8776'_344 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_344 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_346 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_346 v2
du_'8818''45'resp'45''8776'_346 ::
  T_SemiMetric_284 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_346 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_348 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_348 v2
du_'8818''45'resp'691''45''8776'_348 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_348 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_350 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_350 v2
du_'8818''45'resp'737''45''8776'_350 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_350 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_354 ~v0 ~v1 v2
  = du_isPartialEquivalence_354 v2
du_isPartialEquivalence_354 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_354 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.refl
d_refl_356 :: T_SemiMetric_284 -> AgdaAny -> AgdaAny
d_refl_356 v0
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
                  (coe d_isSemiMetric_304 (coe v0))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.reflexive
d_reflexive_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_358 ~v0 ~v1 v2 = du_reflexive_358 v2
du_reflexive_358 ::
  T_SemiMetric_284 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_358 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.sym
d_sym_360 ::
  T_SemiMetric_284 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_360 v0
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
                  (coe d_isSemiMetric_304 (coe v0))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.trans
d_trans_362 ::
  T_SemiMetric_284 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_362 v0
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
                  (coe d_isSemiMetric_304 (coe v0))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_366 ~v0 ~v1 v2
  = du_isPartialEquivalence_366 v2
du_isPartialEquivalence_366 ::
  T_SemiMetric_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_366 v0
  = let v1 = d_isSemiMetric_304 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.refl
d_refl_368 ::
  T_SemiMetric_284 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_368 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.reflexive
d_reflexive_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_370 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.sym
d_sym_372 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_372 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.trans
d_trans_374 ::
  T_SemiMetric_284 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_374 = erased
-- Function.Metric.Nat.Bundles.SemiMetric.quasiSemiMetric
d_quasiSemiMetric_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 -> T_QuasiSemiMetric_186
d_quasiSemiMetric_376 ~v0 ~v1 v2 = du_quasiSemiMetric_376 v2
du_quasiSemiMetric_376 :: T_SemiMetric_284 -> T_QuasiSemiMetric_186
du_quasiSemiMetric_376 v0
  = coe
      C_QuasiSemiMetric'46'constructor_3255 (d_d_302 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe d_isSemiMetric_304 (coe v0)))
-- Function.Metric.Nat.Bundles.SemiMetric._.preMetric
d_preMetric_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 -> T_PreMetric_96
d_preMetric_380 ~v0 ~v1 v2 = du_preMetric_380 v2
du_preMetric_380 :: T_SemiMetric_284 -> T_PreMetric_96
du_preMetric_380 v0
  = coe du_preMetric_274 (coe du_quasiSemiMetric_376 (coe v0))
-- Function.Metric.Nat.Bundles.SemiMetric._.protoMetric
d_protoMetric_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_284 -> T_ProtoMetric_12
d_protoMetric_382 ~v0 ~v1 v2 = du_protoMetric_382 v2
du_protoMetric_382 :: T_SemiMetric_284 -> T_ProtoMetric_12
du_protoMetric_382 v0
  = let v1 = coe du_quasiSemiMetric_376 (coe v0) in
    coe (coe du_protoMetric_180 (coe du_preMetric_274 (coe v1)))
-- Function.Metric.Nat.Bundles.Metric
d_Metric_388 a0 a1 = ()
data T_Metric_388
  = C_Metric'46'constructor_6797 (AgdaAny -> AgdaAny -> Integer)
                                 MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_332
-- Function.Metric.Nat.Bundles.Metric.Carrier
d_Carrier_402 :: T_Metric_388 -> ()
d_Carrier_402 = erased
-- Function.Metric.Nat.Bundles.Metric._≈_
d__'8776'__404 :: T_Metric_388 -> AgdaAny -> AgdaAny -> ()
d__'8776'__404 = erased
-- Function.Metric.Nat.Bundles.Metric.d
d_d_406 :: T_Metric_388 -> AgdaAny -> AgdaAny -> Integer
d_d_406 v0
  = case coe v0 of
      C_Metric'46'constructor_6797 v3 v4 -> coe v3
      _                                  -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.Metric.isMetric
d_isMetric_408 ::
  T_Metric_388 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_332
d_isMetric_408 v0
  = case coe v0 of
      C_Metric'46'constructor_6797 v3 v4 -> coe v4
      _                                  -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.Metric._.0⇒≈
d_0'8658''8776'_412 ::
  T_Metric_388 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_412 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
            (coe d_isMetric_408 (coe v0))))
-- Function.Metric.Nat.Bundles.Metric._.antisym
d_antisym_414 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_414 = erased
-- Function.Metric.Nat.Bundles.Metric._.cong
d_cong_416 ::
  T_Metric_388 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_416 = erased
-- Function.Metric.Nat.Bundles.Metric._.isEquivalence
d_isEquivalence_418 ::
  T_Metric_388 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_418 v0
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
                        (coe d_isMetric_408 (coe v0))))))))
-- Function.Metric.Nat.Bundles.Metric._.isPartialOrder
d_isPartialOrder_420 ::
  T_Metric_388 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_420 v0
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
                  (coe d_isMetric_408 (coe v0))))))
-- Function.Metric.Nat.Bundles.Metric._.isPreMetric
d_isPreMetric_422 ::
  T_Metric_388 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_422 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
            (coe d_isMetric_408 (coe v0))))
-- Function.Metric.Nat.Bundles.Metric._.isPreorder
d_isPreorder_424 ::
  T_Metric_388 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_424 v0
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
                     (coe d_isMetric_408 (coe v0)))))))
-- Function.Metric.Nat.Bundles.Metric._.isProtoMetric
d_isProtoMetric_426 ::
  T_Metric_388 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_426 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
               (coe d_isMetric_408 (coe v0)))))
-- Function.Metric.Nat.Bundles.Metric._.isQuasiSemiMetric
d_isQuasiSemiMetric_428 ::
  T_Metric_388 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_428 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
         (coe d_isMetric_408 (coe v0)))
-- Function.Metric.Nat.Bundles.Metric._.isSemiMetric
d_isSemiMetric_430 ::
  T_Metric_388 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_250
d_isSemiMetric_430 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
      (coe d_isMetric_408 (coe v0))
-- Function.Metric.Nat.Bundles.Metric._.nonNegative
d_nonNegative_432 ::
  T_Metric_388 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_432 v0
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
                  (coe d_isMetric_408 (coe v0))))))
-- Function.Metric.Nat.Bundles.Metric._.refl
d_refl_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_434 ~v0 ~v1 v2 = du_refl_434 v2
du_refl_434 ::
  T_Metric_388 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_434 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.reflexive
d_reflexive_436 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_436 v0
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
                        (coe d_isMetric_408 (coe v0))))))))
-- Function.Metric.Nat.Bundles.Metric._.sym
d_sym_438 ::
  T_Metric_388 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_438 = erased
-- Function.Metric.Nat.Bundles.Metric._.trans
d_trans_440 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_440 v0
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
                        (coe d_isMetric_408 (coe v0))))))))
-- Function.Metric.Nat.Bundles.Metric._.triangle
d_triangle_442 ::
  T_Metric_388 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_triangle_442 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_triangle_344
      (coe d_isMetric_408 (coe v0))
-- Function.Metric.Nat.Bundles.Metric._.≈-isEquivalence
d_'8776''45'isEquivalence_444 ::
  T_Metric_388 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_444 v0
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
                  (coe d_isMetric_408 (coe v0))))))
-- Function.Metric.Nat.Bundles.Metric._.≈⇒0
d_'8776''8658'0_446 ::
  T_Metric_388 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_446 = erased
-- Function.Metric.Nat.Bundles.Metric._.∼-resp-≈
d_'8764''45'resp'45''8776'_448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_448 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_448 v2
du_'8764''45'resp'45''8776'_448 ::
  T_Metric_388 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_448 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_450 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_450 v2
du_'8764''45'resp'691''45''8776'_450 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_450 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_452 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_452 v2
du_'8764''45'resp'737''45''8776'_452 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_452 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.≲-resp-≈
d_'8818''45'resp'45''8776'_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_454 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_454 v2
du_'8818''45'resp'45''8776'_454 ::
  T_Metric_388 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_454 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_456 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_456 v2
du_'8818''45'resp'691''45''8776'_456 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_456 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_458 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_458 v2
du_'8818''45'resp'737''45''8776'_458 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_458 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.EqC.isPartialEquivalence
d_isPartialEquivalence_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_462 ~v0 ~v1 v2
  = du_isPartialEquivalence_462 v2
du_isPartialEquivalence_462 ::
  T_Metric_388 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_462 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.EqC.refl
d_refl_464 :: T_Metric_388 -> AgdaAny -> AgdaAny
d_refl_464 v0
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
                     (coe d_isMetric_408 (coe v0)))))))
-- Function.Metric.Nat.Bundles.Metric._.EqC.reflexive
d_reflexive_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_466 ~v0 ~v1 v2 = du_reflexive_466 v2
du_reflexive_466 ::
  T_Metric_388 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_466 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.EqC.sym
d_sym_468 ::
  T_Metric_388 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_468 v0
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
                     (coe d_isMetric_408 (coe v0)))))))
-- Function.Metric.Nat.Bundles.Metric._.EqC.trans
d_trans_470 ::
  T_Metric_388 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_470 v0
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
                     (coe d_isMetric_408 (coe v0)))))))
-- Function.Metric.Nat.Bundles.Metric._.Eq.isPartialEquivalence
d_isPartialEquivalence_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_474 ~v0 ~v1 v2
  = du_isPartialEquivalence_474 v2
du_isPartialEquivalence_474 ::
  T_Metric_388 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_474 v0
  = let v1 = d_isMetric_408 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.Eq.refl
d_refl_476 ::
  T_Metric_388 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_476 = erased
-- Function.Metric.Nat.Bundles.Metric._.Eq.reflexive
d_reflexive_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_478 = erased
-- Function.Metric.Nat.Bundles.Metric._.Eq.sym
d_sym_480 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_480 = erased
-- Function.Metric.Nat.Bundles.Metric._.Eq.trans
d_trans_482 ::
  T_Metric_388 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_482 = erased
-- Function.Metric.Nat.Bundles.Metric.semiMetric
d_semiMetric_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 -> T_SemiMetric_284
d_semiMetric_484 ~v0 ~v1 v2 = du_semiMetric_484 v2
du_semiMetric_484 :: T_Metric_388 -> T_SemiMetric_284
du_semiMetric_484 v0
  = coe
      C_SemiMetric'46'constructor_4991 (d_d_406 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
         (coe d_isMetric_408 (coe v0)))
-- Function.Metric.Nat.Bundles.Metric._.preMetric
d_preMetric_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 -> T_PreMetric_96
d_preMetric_488 ~v0 ~v1 v2 = du_preMetric_488 v2
du_preMetric_488 :: T_Metric_388 -> T_PreMetric_96
du_preMetric_488 v0
  = let v1 = coe du_semiMetric_484 (coe v0) in
    coe (coe du_preMetric_274 (coe du_quasiSemiMetric_376 (coe v1)))
-- Function.Metric.Nat.Bundles.Metric._.protoMetric
d_protoMetric_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 -> T_ProtoMetric_12
d_protoMetric_490 ~v0 ~v1 v2 = du_protoMetric_490 v2
du_protoMetric_490 :: T_Metric_388 -> T_ProtoMetric_12
du_protoMetric_490 v0
  = let v1 = coe du_semiMetric_484 (coe v0) in
    coe
      (let v2 = coe du_quasiSemiMetric_376 (coe v1) in
       coe (coe du_protoMetric_180 (coe du_preMetric_274 (coe v2))))
-- Function.Metric.Nat.Bundles.Metric._.quasiSemiMetric
d_quasiSemiMetric_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_388 -> T_QuasiSemiMetric_186
d_quasiSemiMetric_492 ~v0 ~v1 v2 = du_quasiSemiMetric_492 v2
du_quasiSemiMetric_492 :: T_Metric_388 -> T_QuasiSemiMetric_186
du_quasiSemiMetric_492 v0
  = coe du_quasiSemiMetric_376 (coe du_semiMetric_484 (coe v0))
-- Function.Metric.Nat.Bundles.UltraMetric
d_UltraMetric_498 a0 a1 = ()
data T_UltraMetric_498
  = C_UltraMetric'46'constructor_8503 (AgdaAny -> AgdaAny -> Integer)
                                      MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_332
-- Function.Metric.Nat.Bundles.UltraMetric.Carrier
d_Carrier_512 :: T_UltraMetric_498 -> ()
d_Carrier_512 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._≈_
d__'8776'__514 :: T_UltraMetric_498 -> AgdaAny -> AgdaAny -> ()
d__'8776'__514 = erased
-- Function.Metric.Nat.Bundles.UltraMetric.d
d_d_516 :: T_UltraMetric_498 -> AgdaAny -> AgdaAny -> Integer
d_d_516 v0
  = case coe v0 of
      C_UltraMetric'46'constructor_8503 v3 v4 -> coe v3
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.UltraMetric.isUltraMetric
d_isUltraMetric_518 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_332
d_isUltraMetric_518 v0
  = case coe v0 of
      C_UltraMetric'46'constructor_8503 v3 v4 -> coe v4
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.UltraMetric._.0⇒≈
d_0'8658''8776'_522 ::
  T_UltraMetric_498 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_522 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_184
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
            (coe d_isUltraMetric_518 (coe v0))))
-- Function.Metric.Nat.Bundles.UltraMetric._.antisym
d_antisym_524 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_524 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.cong
d_cong_526 ::
  T_UltraMetric_498 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_526 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.isEquivalence
d_isEquivalence_528 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_528 v0
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
                        (coe d_isUltraMetric_518 (coe v0))))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isPartialOrder
d_isPartialOrder_530 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_530 v0
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
                  (coe d_isUltraMetric_518 (coe v0))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isPreMetric
d_isPreMetric_532 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_isPreMetric_532 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
            (coe d_isUltraMetric_518 (coe v0))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isPreorder
d_isPreorder_534 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_534 v0
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
                     (coe d_isUltraMetric_518 (coe v0)))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isProtoMetric
d_isProtoMetric_536 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_536 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_110
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_182
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
               (coe d_isUltraMetric_518 (coe v0)))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_538 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
d_isQuasiSemiMetric_538 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_258
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
         (coe d_isUltraMetric_518 (coe v0)))
-- Function.Metric.Nat.Bundles.UltraMetric._.isSemiMetric
d_isSemiMetric_540 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_250
d_isSemiMetric_540 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
      (coe d_isUltraMetric_518 (coe v0))
-- Function.Metric.Nat.Bundles.UltraMetric._.nonNegative
d_nonNegative_542 ::
  T_UltraMetric_498 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_542 v0
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
                  (coe d_isUltraMetric_518 (coe v0))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.refl
d_refl_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_544 ~v0 ~v1 v2 = du_refl_544 v2
du_refl_544 ::
  T_UltraMetric_498 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_544 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.reflexive
d_reflexive_546 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_546 v0
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
                        (coe d_isUltraMetric_518 (coe v0))))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.sym
d_sym_548 ::
  T_UltraMetric_498 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_548 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.trans
d_trans_550 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_550 v0
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
                        (coe d_isUltraMetric_518 (coe v0))))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.triangle
d_triangle_552 ::
  T_UltraMetric_498 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_triangle_552 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_triangle_344
      (coe d_isUltraMetric_518 (coe v0))
-- Function.Metric.Nat.Bundles.UltraMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_554 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_554 v0
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
                  (coe d_isUltraMetric_518 (coe v0))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.≈⇒0
d_'8776''8658'0_556 ::
  T_UltraMetric_498 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_556 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_558 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_558 v2
du_'8764''45'resp'45''8776'_558 ::
  T_UltraMetric_498 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_558 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_560 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_560 v2
du_'8764''45'resp'691''45''8776'_560 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_560 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_562 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_562 v2
du_'8764''45'resp'737''45''8776'_562 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_562 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_564 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_564 v2
du_'8818''45'resp'45''8776'_564 ::
  T_UltraMetric_498 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_564 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_566 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_566 v2
du_'8818''45'resp'691''45''8776'_566 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_566 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_568 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_568 v2
du_'8818''45'resp'737''45''8776'_568 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_568 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_572 ~v0 ~v1 v2
  = du_isPartialEquivalence_572 v2
du_isPartialEquivalence_572 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_572 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.refl
d_refl_574 :: T_UltraMetric_498 -> AgdaAny -> AgdaAny
d_refl_574 v0
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
                     (coe d_isUltraMetric_518 (coe v0)))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.reflexive
d_reflexive_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_576 ~v0 ~v1 v2 = du_reflexive_576 v2
du_reflexive_576 ::
  T_UltraMetric_498 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_576 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.sym
d_sym_578 ::
  T_UltraMetric_498 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_578 v0
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
                     (coe d_isUltraMetric_518 (coe v0)))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.trans
d_trans_580 ::
  T_UltraMetric_498 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_580 v0
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
                     (coe d_isUltraMetric_518 (coe v0)))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_584 ~v0 ~v1 v2
  = du_isPartialEquivalence_584 v2
du_isPartialEquivalence_584 ::
  T_UltraMetric_498 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_584 v0
  = let v1 = d_isUltraMetric_518 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.refl
d_refl_586 ::
  T_UltraMetric_498 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_586 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.reflexive
d_reflexive_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_588 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.sym
d_sym_590 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_590 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.trans
d_trans_592 ::
  T_UltraMetric_498 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_592 = erased
-- Function.Metric.Nat.Bundles.UltraMetric.semiMetric
d_semiMetric_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 -> T_SemiMetric_284
d_semiMetric_594 ~v0 ~v1 v2 = du_semiMetric_594 v2
du_semiMetric_594 :: T_UltraMetric_498 -> T_SemiMetric_284
du_semiMetric_594 v0
  = coe
      C_SemiMetric'46'constructor_4991 (d_d_516 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_342
         (coe d_isUltraMetric_518 (coe v0)))
-- Function.Metric.Nat.Bundles.UltraMetric._.preMetric
d_preMetric_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 -> T_PreMetric_96
d_preMetric_598 ~v0 ~v1 v2 = du_preMetric_598 v2
du_preMetric_598 :: T_UltraMetric_498 -> T_PreMetric_96
du_preMetric_598 v0
  = let v1 = coe du_semiMetric_594 (coe v0) in
    coe (coe du_preMetric_274 (coe du_quasiSemiMetric_376 (coe v1)))
-- Function.Metric.Nat.Bundles.UltraMetric._.protoMetric
d_protoMetric_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 -> T_ProtoMetric_12
d_protoMetric_600 ~v0 ~v1 v2 = du_protoMetric_600 v2
du_protoMetric_600 :: T_UltraMetric_498 -> T_ProtoMetric_12
du_protoMetric_600 v0
  = let v1 = coe du_semiMetric_594 (coe v0) in
    coe
      (let v2 = coe du_quasiSemiMetric_376 (coe v1) in
       coe (coe du_protoMetric_180 (coe du_preMetric_274 (coe v2))))
-- Function.Metric.Nat.Bundles.UltraMetric._.quasiSemiMetric
d_quasiSemiMetric_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_498 -> T_QuasiSemiMetric_186
d_quasiSemiMetric_602 ~v0 ~v1 v2 = du_quasiSemiMetric_602 v2
du_quasiSemiMetric_602 ::
  T_UltraMetric_498 -> T_QuasiSemiMetric_186
du_quasiSemiMetric_602 v0
  = coe du_quasiSemiMetric_376 (coe du_semiMetric_594 (coe v0))
