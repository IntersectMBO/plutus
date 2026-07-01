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

module MAlonzo.Code.Function.Metric.Nat.Bundles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Function.Metric.Structures
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Function.Metric.Nat.Bundles.ProtoMetric
d_ProtoMetric_12 a0 a1 = ()
data T_ProtoMetric_12
  = C_constructor_92 (AgdaAny -> AgdaAny -> Integer)
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
      C_constructor_92 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.ProtoMetric.isProtoMetric
d_isProtoMetric_32 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_32 v0
  = case coe v0 of
      C_constructor_92 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_40 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_32 (coe v0))))
-- Function.Metric.Nat.Bundles.ProtoMetric._.isPartialOrder
d_isPartialOrder_42 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_42 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe d_isProtoMetric_32 (coe v0))
-- Function.Metric.Nat.Bundles.ProtoMetric._.isPreorder
d_isPreorder_44 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_44 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe d_isProtoMetric_32 (coe v0))))
-- Function.Metric.Nat.Bundles.ProtoMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_54 ::
  T_ProtoMetric_12 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
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
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
            (coe v1)))
-- Function.Metric.Nat.Bundles.ProtoMetric._.EqC.refl
d_refl_72 :: T_ProtoMetric_12 -> AgdaAny -> AgdaAny
d_refl_72 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
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
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe
              MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
              (coe v1))
           v2)
-- Function.Metric.Nat.Bundles.ProtoMetric._.EqC.sym
d_sym_76 ::
  T_ProtoMetric_12 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_76 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe d_isProtoMetric_32 (coe v0)))
-- Function.Metric.Nat.Bundles.ProtoMetric._.EqC.trans
d_trans_78 ::
  T_ProtoMetric_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
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
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
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
d_PreMetric_98 a0 a1 = ()
data T_PreMetric_98
  = C_constructor_184 (AgdaAny -> AgdaAny -> Integer)
                      MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
-- Function.Metric.Nat.Bundles.PreMetric.Carrier
d_Carrier_112 :: T_PreMetric_98 -> ()
d_Carrier_112 = erased
-- Function.Metric.Nat.Bundles.PreMetric._≈_
d__'8776'__114 :: T_PreMetric_98 -> AgdaAny -> AgdaAny -> ()
d__'8776'__114 = erased
-- Function.Metric.Nat.Bundles.PreMetric.d
d_d_116 :: T_PreMetric_98 -> AgdaAny -> AgdaAny -> Integer
d_d_116 v0
  = case coe v0 of
      C_constructor_184 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.PreMetric.isPreMetric
d_isPreMetric_118 ::
  T_PreMetric_98 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_118 v0
  = case coe v0 of
      C_constructor_184 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.PreMetric._.antisym
d_antisym_122 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_122 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.cong
d_cong_124 ::
  T_PreMetric_98 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_124 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.isEquivalence
d_isEquivalence_126 ::
  T_PreMetric_98 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_126 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe d_isPreMetric_118 (coe v0)))))
-- Function.Metric.Nat.Bundles.PreMetric._.isPartialOrder
d_isPartialOrder_128 ::
  T_PreMetric_98 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_128 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_118 (coe v0)))
-- Function.Metric.Nat.Bundles.PreMetric._.isPreorder
d_isPreorder_130 ::
  T_PreMetric_98 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_130 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_118 (coe v0))))
-- Function.Metric.Nat.Bundles.PreMetric._.isProtoMetric
d_isProtoMetric_132 ::
  T_PreMetric_98 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_132 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe d_isPreMetric_118 (coe v0))
-- Function.Metric.Nat.Bundles.PreMetric._.nonNegative
d_nonNegative_134 ::
  T_PreMetric_98 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_134 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_118 (coe v0)))
-- Function.Metric.Nat.Bundles.PreMetric._.refl
d_refl_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_136 ~v0 ~v1 v2 = du_refl_136 v2
du_refl_136 ::
  T_PreMetric_98 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_136 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.reflexive
d_reflexive_138 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_138 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe d_isPreMetric_118 (coe v0)))))
-- Function.Metric.Nat.Bundles.PreMetric._.trans
d_trans_140 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_140 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
               (coe d_isPreMetric_118 (coe v0)))))
-- Function.Metric.Nat.Bundles.PreMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_142 ::
  T_PreMetric_98 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_142 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_118 (coe v0)))
-- Function.Metric.Nat.Bundles.PreMetric._.≈⇒0
d_'8776''8658'0_144 ::
  T_PreMetric_98 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_144 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_146 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_146 v2
du_'8764''45'resp'45''8776'_146 ::
  T_PreMetric_98 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_146 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_148 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_148 v2
du_'8764''45'resp'691''45''8776'_148 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_148 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_150 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_150 v2
du_'8764''45'resp'737''45''8776'_150 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_150 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_152 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_152 v2
du_'8818''45'resp'45''8776'_152 ::
  T_PreMetric_98 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_152 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_154 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_154 v2
du_'8818''45'resp'691''45''8776'_154 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_154 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_156 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_156 v2
du_'8818''45'resp'737''45''8776'_156 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_156 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_160 ~v0 ~v1 v2
  = du_isPartialEquivalence_160 v2
du_isPartialEquivalence_160 ::
  T_PreMetric_98 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_160 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.refl
d_refl_162 :: T_PreMetric_98 -> AgdaAny -> AgdaAny
d_refl_162 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_118 (coe v0))))
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.reflexive
d_reflexive_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_164 ~v0 ~v1 v2 = du_reflexive_164 v2
du_reflexive_164 ::
  T_PreMetric_98 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_164 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.sym
d_sym_166 ::
  T_PreMetric_98 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_166 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_118 (coe v0))))
-- Function.Metric.Nat.Bundles.PreMetric._.EqC.trans
d_trans_168 ::
  T_PreMetric_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_168 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe d_isPreMetric_118 (coe v0))))
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_172 ~v0 ~v1 v2
  = du_isPartialEquivalence_172 v2
du_isPartialEquivalence_172 ::
  T_PreMetric_98 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_172 v0
  = let v1 = d_isPreMetric_118 (coe v0) in
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
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.refl
d_refl_174 ::
  T_PreMetric_98 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_174 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.reflexive
d_reflexive_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_176 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.sym
d_sym_178 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_178 = erased
-- Function.Metric.Nat.Bundles.PreMetric._.Eq.trans
d_trans_180 ::
  T_PreMetric_98 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_180 = erased
-- Function.Metric.Nat.Bundles.PreMetric.protoMetric
d_protoMetric_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_PreMetric_98 -> T_ProtoMetric_12
d_protoMetric_182 ~v0 ~v1 v2 = du_protoMetric_182 v2
du_protoMetric_182 :: T_PreMetric_98 -> T_ProtoMetric_12
du_protoMetric_182 v0
  = coe
      C_constructor_92 (d_d_116 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe d_isPreMetric_118 (coe v0)))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric
d_QuasiSemiMetric_190 a0 a1 = ()
data T_QuasiSemiMetric_190
  = C_constructor_284 (AgdaAny -> AgdaAny -> Integer)
                      MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
-- Function.Metric.Nat.Bundles.QuasiSemiMetric.Carrier
d_Carrier_204 :: T_QuasiSemiMetric_190 -> ()
d_Carrier_204 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._≈_
d__'8776'__206 :: T_QuasiSemiMetric_190 -> AgdaAny -> AgdaAny -> ()
d__'8776'__206 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric.d
d_d_208 :: T_QuasiSemiMetric_190 -> AgdaAny -> AgdaAny -> Integer
d_d_208 v0
  = case coe v0 of
      C_constructor_284 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.QuasiSemiMetric.isQuasiSemiMetric
d_isQuasiSemiMetric_210 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_210 v0
  = case coe v0 of
      C_constructor_284 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.0⇒≈
d_0'8658''8776'_214 ::
  T_QuasiSemiMetric_190 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_214 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe d_isQuasiSemiMetric_210 (coe v0))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.antisym
d_antisym_216 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_216 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.cong
d_cong_218 ::
  T_QuasiSemiMetric_190 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_218 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isEquivalence
d_isEquivalence_220 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_220 v0
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
                  (coe d_isQuasiSemiMetric_210 (coe v0))))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isPartialOrder
d_isPartialOrder_222 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_222 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe d_isQuasiSemiMetric_210 (coe v0))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isPreMetric
d_isPreMetric_224 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_224 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe d_isQuasiSemiMetric_210 (coe v0))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isPreorder
d_isPreorder_226 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_226 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_210 (coe v0)))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.isProtoMetric
d_isProtoMetric_228 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_228 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe d_isQuasiSemiMetric_210 (coe v0)))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.nonNegative
d_nonNegative_230 ::
  T_QuasiSemiMetric_190 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_230 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe d_isQuasiSemiMetric_210 (coe v0))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.refl
d_refl_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_232 ~v0 ~v1 v2 = du_refl_232 v2
du_refl_232 ::
  T_QuasiSemiMetric_190 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_232 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.reflexive
d_reflexive_234 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_234 v0
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
                  (coe d_isQuasiSemiMetric_210 (coe v0))))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.trans
d_trans_236 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_236 v0
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
                  (coe d_isQuasiSemiMetric_210 (coe v0))))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_238 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_238 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe d_isQuasiSemiMetric_210 (coe v0))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≈⇒0
d_'8776''8658'0_240 ::
  T_QuasiSemiMetric_190 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_240 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_242 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_242 v2
du_'8764''45'resp'45''8776'_242 ::
  T_QuasiSemiMetric_190 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_242 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_244 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_244 v2
du_'8764''45'resp'691''45''8776'_244 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_244 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_246 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_246 v2
du_'8764''45'resp'737''45''8776'_246 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_246 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_248 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_248 v2
du_'8818''45'resp'45''8776'_248 ::
  T_QuasiSemiMetric_190 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_248 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_250 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_250 v2
du_'8818''45'resp'691''45''8776'_250 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_250 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_252 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_252 v2
du_'8818''45'resp'737''45''8776'_252 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_252 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_256 ~v0 ~v1 v2
  = du_isPartialEquivalence_256 v2
du_isPartialEquivalence_256 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_256 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.refl
d_refl_258 :: T_QuasiSemiMetric_190 -> AgdaAny -> AgdaAny
d_refl_258 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_210 (coe v0)))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.reflexive
d_reflexive_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_260 ~v0 ~v1 v2 = du_reflexive_260 v2
du_reflexive_260 ::
  T_QuasiSemiMetric_190 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_260 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.sym
d_sym_262 ::
  T_QuasiSemiMetric_190 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_262 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_210 (coe v0)))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.EqC.trans
d_trans_264 ::
  T_QuasiSemiMetric_190 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_264 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
               (coe d_isQuasiSemiMetric_210 (coe v0)))))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_268 ~v0 ~v1 v2
  = du_isPartialEquivalence_268 v2
du_isPartialEquivalence_268 ::
  T_QuasiSemiMetric_190 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_268 v0
  = let v1 = d_isQuasiSemiMetric_210 (coe v0) in
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
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.refl
d_refl_270 ::
  T_QuasiSemiMetric_190 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_270 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.reflexive
d_reflexive_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_272 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.sym
d_sym_274 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_274 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.Eq.trans
d_trans_276 ::
  T_QuasiSemiMetric_190 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_276 = erased
-- Function.Metric.Nat.Bundles.QuasiSemiMetric.preMetric
d_preMetric_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 -> T_PreMetric_98
d_preMetric_278 ~v0 ~v1 v2 = du_preMetric_278 v2
du_preMetric_278 :: T_QuasiSemiMetric_190 -> T_PreMetric_98
du_preMetric_278 v0
  = coe
      C_constructor_184 (d_d_208 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe d_isQuasiSemiMetric_210 (coe v0)))
-- Function.Metric.Nat.Bundles.QuasiSemiMetric._.protoMetric
d_protoMetric_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_QuasiSemiMetric_190 -> T_ProtoMetric_12
d_protoMetric_282 ~v0 ~v1 v2 = du_protoMetric_282 v2
du_protoMetric_282 :: T_QuasiSemiMetric_190 -> T_ProtoMetric_12
du_protoMetric_282 v0
  = coe du_protoMetric_182 (coe du_preMetric_278 (coe v0))
-- Function.Metric.Nat.Bundles.SemiMetric
d_SemiMetric_290 a0 a1 = ()
data T_SemiMetric_290
  = C_constructor_390 (AgdaAny -> AgdaAny -> Integer)
                      MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
-- Function.Metric.Nat.Bundles.SemiMetric.Carrier
d_Carrier_304 :: T_SemiMetric_290 -> ()
d_Carrier_304 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._≈_
d__'8776'__306 :: T_SemiMetric_290 -> AgdaAny -> AgdaAny -> ()
d__'8776'__306 = erased
-- Function.Metric.Nat.Bundles.SemiMetric.d
d_d_308 :: T_SemiMetric_290 -> AgdaAny -> AgdaAny -> Integer
d_d_308 v0
  = case coe v0 of
      C_constructor_390 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.SemiMetric.isSemiMetric
d_isSemiMetric_310 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
d_isSemiMetric_310 v0
  = case coe v0 of
      C_constructor_390 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.SemiMetric._.0⇒≈
d_0'8658''8776'_314 ::
  T_SemiMetric_290 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_314 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe d_isSemiMetric_310 (coe v0)))
-- Function.Metric.Nat.Bundles.SemiMetric._.antisym
d_antisym_316 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_316 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.cong
d_cong_318 ::
  T_SemiMetric_290 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_318 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.isEquivalence
d_isEquivalence_320 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_320 v0
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
                     (coe d_isSemiMetric_310 (coe v0)))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.isPartialOrder
d_isPartialOrder_322 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_322 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPartialOrder_42
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe d_isSemiMetric_310 (coe v0)))))
-- Function.Metric.Nat.Bundles.SemiMetric._.isPreMetric
d_isPreMetric_324 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_324 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe d_isSemiMetric_310 (coe v0)))
-- Function.Metric.Nat.Bundles.SemiMetric._.isPreorder
d_isPreorder_326 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_326 v0
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
                  (coe d_isSemiMetric_310 (coe v0))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.isProtoMetric
d_isProtoMetric_328 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_328 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe d_isSemiMetric_310 (coe v0))))
-- Function.Metric.Nat.Bundles.SemiMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_330 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_330 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
      (coe d_isSemiMetric_310 (coe v0))
-- Function.Metric.Nat.Bundles.SemiMetric._.nonNegative
d_nonNegative_332 ::
  T_SemiMetric_290 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_332 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_nonNegative_48
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe d_isSemiMetric_310 (coe v0)))))
-- Function.Metric.Nat.Bundles.SemiMetric._.refl
d_refl_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_334 ~v0 ~v1 v2 = du_refl_334 v2
du_refl_334 ::
  T_SemiMetric_290 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_334 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.reflexive
d_reflexive_336 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_336 v0
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
                     (coe d_isSemiMetric_310 (coe v0)))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.sym
d_sym_338 ::
  T_SemiMetric_290 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_338 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.trans
d_trans_340 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_340 v0
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
                     (coe d_isSemiMetric_310 (coe v0)))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_342 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_342 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_'8776''45'isEquivalence_44
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
               (coe d_isSemiMetric_310 (coe v0)))))
-- Function.Metric.Nat.Bundles.SemiMetric._.≈⇒0
d_'8776''8658'0_344 ::
  T_SemiMetric_290 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_344 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_346 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_346 v2
du_'8764''45'resp'45''8776'_346 ::
  T_SemiMetric_290 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_346 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_348 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_348 v2
du_'8764''45'resp'691''45''8776'_348 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_348 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_350 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_350 v2
du_'8764''45'resp'737''45''8776'_350 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_350 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_352 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_352 v2
du_'8818''45'resp'45''8776'_352 ::
  T_SemiMetric_290 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_352 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_354 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_354 v2
du_'8818''45'resp'691''45''8776'_354 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_354 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_356 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_356 v2
du_'8818''45'resp'737''45''8776'_356 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_356 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_360 ~v0 ~v1 v2
  = du_isPartialEquivalence_360 v2
du_isPartialEquivalence_360 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_360 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.refl
d_refl_362 :: T_SemiMetric_290 -> AgdaAny -> AgdaAny
d_refl_362 v0
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
                  (coe d_isSemiMetric_310 (coe v0))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.reflexive
d_reflexive_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_364 ~v0 ~v1 v2 = du_reflexive_364 v2
du_reflexive_364 ::
  T_SemiMetric_290 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_364 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.sym
d_sym_366 ::
  T_SemiMetric_290 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_366 v0
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
                  (coe d_isSemiMetric_310 (coe v0))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.EqC.trans
d_trans_368 ::
  T_SemiMetric_290 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_368 v0
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
                  (coe d_isSemiMetric_310 (coe v0))))))
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_372 ~v0 ~v1 v2
  = du_isPartialEquivalence_372 v2
du_isPartialEquivalence_372 ::
  T_SemiMetric_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_372 v0
  = let v1 = d_isSemiMetric_310 (coe v0) in
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
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.refl
d_refl_374 ::
  T_SemiMetric_290 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_374 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.reflexive
d_reflexive_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_376 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.sym
d_sym_378 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_378 = erased
-- Function.Metric.Nat.Bundles.SemiMetric._.Eq.trans
d_trans_380 ::
  T_SemiMetric_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_380 = erased
-- Function.Metric.Nat.Bundles.SemiMetric.quasiSemiMetric
d_quasiSemiMetric_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 -> T_QuasiSemiMetric_190
d_quasiSemiMetric_382 ~v0 ~v1 v2 = du_quasiSemiMetric_382 v2
du_quasiSemiMetric_382 :: T_SemiMetric_290 -> T_QuasiSemiMetric_190
du_quasiSemiMetric_382 v0
  = coe
      C_constructor_284 (d_d_308 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe d_isSemiMetric_310 (coe v0)))
-- Function.Metric.Nat.Bundles.SemiMetric._.preMetric
d_preMetric_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 -> T_PreMetric_98
d_preMetric_386 ~v0 ~v1 v2 = du_preMetric_386 v2
du_preMetric_386 :: T_SemiMetric_290 -> T_PreMetric_98
du_preMetric_386 v0
  = coe du_preMetric_278 (coe du_quasiSemiMetric_382 (coe v0))
-- Function.Metric.Nat.Bundles.SemiMetric._.protoMetric
d_protoMetric_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_SemiMetric_290 -> T_ProtoMetric_12
d_protoMetric_388 ~v0 ~v1 v2 = du_protoMetric_388 v2
du_protoMetric_388 :: T_SemiMetric_290 -> T_ProtoMetric_12
du_protoMetric_388 v0
  = let v1 = coe du_quasiSemiMetric_382 (coe v0) in
    coe (coe du_protoMetric_182 (coe du_preMetric_278 (coe v1)))
-- Function.Metric.Nat.Bundles.Metric
d_Metric_396 a0 a1 = ()
data T_Metric_396
  = C_constructor_502 (AgdaAny -> AgdaAny -> Integer)
                      MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340
-- Function.Metric.Nat.Bundles.Metric.Carrier
d_Carrier_410 :: T_Metric_396 -> ()
d_Carrier_410 = erased
-- Function.Metric.Nat.Bundles.Metric._≈_
d__'8776'__412 :: T_Metric_396 -> AgdaAny -> AgdaAny -> ()
d__'8776'__412 = erased
-- Function.Metric.Nat.Bundles.Metric.d
d_d_414 :: T_Metric_396 -> AgdaAny -> AgdaAny -> Integer
d_d_414 v0
  = case coe v0 of
      C_constructor_502 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.Metric.isMetric
d_isMetric_416 ::
  T_Metric_396 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340
d_isMetric_416 v0
  = case coe v0 of
      C_constructor_502 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.Metric._.0⇒≈
d_0'8658''8776'_420 ::
  T_Metric_396 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_420 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe d_isMetric_416 (coe v0))))
-- Function.Metric.Nat.Bundles.Metric._.antisym
d_antisym_422 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_422 = erased
-- Function.Metric.Nat.Bundles.Metric._.cong
d_cong_424 ::
  T_Metric_396 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_424 = erased
-- Function.Metric.Nat.Bundles.Metric._.isEquivalence
d_isEquivalence_426 ::
  T_Metric_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_426 v0
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
                        (coe d_isMetric_416 (coe v0))))))))
-- Function.Metric.Nat.Bundles.Metric._.isPartialOrder
d_isPartialOrder_428 ::
  T_Metric_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_428 v0
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
                  (coe d_isMetric_416 (coe v0))))))
-- Function.Metric.Nat.Bundles.Metric._.isPreMetric
d_isPreMetric_430 ::
  T_Metric_396 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_430 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe d_isMetric_416 (coe v0))))
-- Function.Metric.Nat.Bundles.Metric._.isPreorder
d_isPreorder_432 ::
  T_Metric_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_432 v0
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
                     (coe d_isMetric_416 (coe v0)))))))
-- Function.Metric.Nat.Bundles.Metric._.isProtoMetric
d_isProtoMetric_434 ::
  T_Metric_396 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_434 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
               (coe d_isMetric_416 (coe v0)))))
-- Function.Metric.Nat.Bundles.Metric._.isQuasiSemiMetric
d_isQuasiSemiMetric_436 ::
  T_Metric_396 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_436 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe d_isMetric_416 (coe v0)))
-- Function.Metric.Nat.Bundles.Metric._.isSemiMetric
d_isSemiMetric_438 ::
  T_Metric_396 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
d_isSemiMetric_438 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
      (coe d_isMetric_416 (coe v0))
-- Function.Metric.Nat.Bundles.Metric._.nonNegative
d_nonNegative_440 ::
  T_Metric_396 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_440 v0
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
                  (coe d_isMetric_416 (coe v0))))))
-- Function.Metric.Nat.Bundles.Metric._.refl
d_refl_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_442 ~v0 ~v1 v2 = du_refl_442 v2
du_refl_442 ::
  T_Metric_396 -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_442 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.reflexive
d_reflexive_444 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_444 v0
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
                        (coe d_isMetric_416 (coe v0))))))))
-- Function.Metric.Nat.Bundles.Metric._.sym
d_sym_446 ::
  T_Metric_396 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_446 = erased
-- Function.Metric.Nat.Bundles.Metric._.trans
d_trans_448 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_448 v0
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
                        (coe d_isMetric_416 (coe v0))))))))
-- Function.Metric.Nat.Bundles.Metric._.triangle
d_triangle_450 ::
  T_Metric_396 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_triangle_450 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_triangle_352
      (coe d_isMetric_416 (coe v0))
-- Function.Metric.Nat.Bundles.Metric._.≈-isEquivalence
d_'8776''45'isEquivalence_452 ::
  T_Metric_396 ->
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
               (coe
                  MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                  (coe d_isMetric_416 (coe v0))))))
-- Function.Metric.Nat.Bundles.Metric._.≈⇒0
d_'8776''8658'0_454 ::
  T_Metric_396 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_454 = erased
-- Function.Metric.Nat.Bundles.Metric._.∼-resp-≈
d_'8764''45'resp'45''8776'_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_456 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_456 v2
du_'8764''45'resp'45''8776'_456 ::
  T_Metric_396 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_456 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_458 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_458 v2
du_'8764''45'resp'691''45''8776'_458 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_458 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_460 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_460 v2
du_'8764''45'resp'737''45''8776'_460 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_460 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.≲-resp-≈
d_'8818''45'resp'45''8776'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_462 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_462 v2
du_'8818''45'resp'45''8776'_462 ::
  T_Metric_396 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_462 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_464 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_464 v2
du_'8818''45'resp'691''45''8776'_464 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_464 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_466 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_466 v2
du_'8818''45'resp'737''45''8776'_466 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_466 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.EqC.isPartialEquivalence
d_isPartialEquivalence_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_470 ~v0 ~v1 v2
  = du_isPartialEquivalence_470 v2
du_isPartialEquivalence_470 ::
  T_Metric_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_470 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.EqC.refl
d_refl_472 :: T_Metric_396 -> AgdaAny -> AgdaAny
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
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                     (coe d_isMetric_416 (coe v0)))))))
-- Function.Metric.Nat.Bundles.Metric._.EqC.reflexive
d_reflexive_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_474 ~v0 ~v1 v2 = du_reflexive_474 v2
du_reflexive_474 ::
  T_Metric_396 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_474 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.EqC.sym
d_sym_476 ::
  T_Metric_396 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
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
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                     (coe d_isMetric_416 (coe v0)))))))
-- Function.Metric.Nat.Bundles.Metric._.EqC.trans
d_trans_478 ::
  T_Metric_396 ->
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
                  (coe
                     MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
                     (coe d_isMetric_416 (coe v0)))))))
-- Function.Metric.Nat.Bundles.Metric._.Eq.isPartialEquivalence
d_isPartialEquivalence_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_482 ~v0 ~v1 v2
  = du_isPartialEquivalence_482 v2
du_isPartialEquivalence_482 ::
  T_Metric_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_482 v0
  = let v1 = d_isMetric_416 (coe v0) in
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
-- Function.Metric.Nat.Bundles.Metric._.Eq.refl
d_refl_484 ::
  T_Metric_396 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_484 = erased
-- Function.Metric.Nat.Bundles.Metric._.Eq.reflexive
d_reflexive_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_486 = erased
-- Function.Metric.Nat.Bundles.Metric._.Eq.sym
d_sym_488 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_488 = erased
-- Function.Metric.Nat.Bundles.Metric._.Eq.trans
d_trans_490 ::
  T_Metric_396 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_490 = erased
-- Function.Metric.Nat.Bundles.Metric.semiMetric
d_semiMetric_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 -> T_SemiMetric_290
d_semiMetric_492 ~v0 ~v1 v2 = du_semiMetric_492 v2
du_semiMetric_492 :: T_Metric_396 -> T_SemiMetric_290
du_semiMetric_492 v0
  = coe
      C_constructor_390 (d_d_414 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe d_isMetric_416 (coe v0)))
-- Function.Metric.Nat.Bundles.Metric._.preMetric
d_preMetric_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 -> T_PreMetric_98
d_preMetric_496 ~v0 ~v1 v2 = du_preMetric_496 v2
du_preMetric_496 :: T_Metric_396 -> T_PreMetric_98
du_preMetric_496 v0
  = let v1 = coe du_semiMetric_492 (coe v0) in
    coe (coe du_preMetric_278 (coe du_quasiSemiMetric_382 (coe v1)))
-- Function.Metric.Nat.Bundles.Metric._.protoMetric
d_protoMetric_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 -> T_ProtoMetric_12
d_protoMetric_498 ~v0 ~v1 v2 = du_protoMetric_498 v2
du_protoMetric_498 :: T_Metric_396 -> T_ProtoMetric_12
du_protoMetric_498 v0
  = let v1 = coe du_semiMetric_492 (coe v0) in
    coe
      (let v2 = coe du_quasiSemiMetric_382 (coe v1) in
       coe (coe du_protoMetric_182 (coe du_preMetric_278 (coe v2))))
-- Function.Metric.Nat.Bundles.Metric._.quasiSemiMetric
d_quasiSemiMetric_500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Metric_396 -> T_QuasiSemiMetric_190
d_quasiSemiMetric_500 ~v0 ~v1 v2 = du_quasiSemiMetric_500 v2
du_quasiSemiMetric_500 :: T_Metric_396 -> T_QuasiSemiMetric_190
du_quasiSemiMetric_500 v0
  = coe du_quasiSemiMetric_382 (coe du_semiMetric_492 (coe v0))
-- Function.Metric.Nat.Bundles.UltraMetric
d_UltraMetric_508 a0 a1 = ()
data T_UltraMetric_508
  = C_constructor_614 (AgdaAny -> AgdaAny -> Integer)
                      MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340
-- Function.Metric.Nat.Bundles.UltraMetric.Carrier
d_Carrier_522 :: T_UltraMetric_508 -> ()
d_Carrier_522 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._≈_
d__'8776'__524 :: T_UltraMetric_508 -> AgdaAny -> AgdaAny -> ()
d__'8776'__524 = erased
-- Function.Metric.Nat.Bundles.UltraMetric.d
d_d_526 :: T_UltraMetric_508 -> AgdaAny -> AgdaAny -> Integer
d_d_526 v0
  = case coe v0 of
      C_constructor_614 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.UltraMetric.isUltraMetric
d_isUltraMetric_528 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340
d_isUltraMetric_528 v0
  = case coe v0 of
      C_constructor_614 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Metric.Nat.Bundles.UltraMetric._.0⇒≈
d_0'8658''8776'_532 ::
  T_UltraMetric_508 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_532 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe d_isUltraMetric_528 (coe v0))))
-- Function.Metric.Nat.Bundles.UltraMetric._.antisym
d_antisym_534 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_534 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.cong
d_cong_536 ::
  T_UltraMetric_508 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_536 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.isEquivalence
d_isEquivalence_538 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_538 v0
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
                        (coe d_isUltraMetric_528 (coe v0))))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isPartialOrder
d_isPartialOrder_540 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_540 v0
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
                  (coe d_isUltraMetric_528 (coe v0))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isPreMetric
d_isPreMetric_542 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_542 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe d_isUltraMetric_528 (coe v0))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isPreorder
d_isPreorder_544 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_544 v0
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
                     (coe d_isUltraMetric_528 (coe v0)))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isProtoMetric
d_isProtoMetric_546 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_546 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
               (coe d_isUltraMetric_528 (coe v0)))))
-- Function.Metric.Nat.Bundles.UltraMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_548 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_548 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe d_isUltraMetric_528 (coe v0)))
-- Function.Metric.Nat.Bundles.UltraMetric._.isSemiMetric
d_isSemiMetric_550 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
d_isSemiMetric_550 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
      (coe d_isUltraMetric_528 (coe v0))
-- Function.Metric.Nat.Bundles.UltraMetric._.nonNegative
d_nonNegative_552 ::
  T_UltraMetric_508 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_552 v0
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
                  (coe d_isUltraMetric_528 (coe v0))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.refl
d_refl_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_554 ~v0 ~v1 v2 = du_refl_554 v2
du_refl_554 ::
  T_UltraMetric_508 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_554 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.reflexive
d_reflexive_556 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_556 v0
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
                        (coe d_isUltraMetric_528 (coe v0))))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.sym
d_sym_558 ::
  T_UltraMetric_508 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_558 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.trans
d_trans_560 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_560 v0
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
                        (coe d_isUltraMetric_528 (coe v0))))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.triangle
d_triangle_562 ::
  T_UltraMetric_508 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_triangle_562 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_triangle_352
      (coe d_isUltraMetric_528 (coe v0))
-- Function.Metric.Nat.Bundles.UltraMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_564 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_564 v0
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
                  (coe d_isUltraMetric_528 (coe v0))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.≈⇒0
d_'8776''8658'0_566 ::
  T_UltraMetric_508 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_566 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_568 ~v0 ~v1 v2
  = du_'8764''45'resp'45''8776'_568 v2
du_'8764''45'resp'45''8776'_568 ::
  T_UltraMetric_508 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_568 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_570 ~v0 ~v1 v2
  = du_'8764''45'resp'691''45''8776'_570 v2
du_'8764''45'resp'691''45''8776'_570 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_570 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_572 ~v0 ~v1 v2
  = du_'8764''45'resp'737''45''8776'_572 v2
du_'8764''45'resp'737''45''8776'_572 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_572 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_574 ~v0 ~v1 v2
  = du_'8818''45'resp'45''8776'_574 v2
du_'8818''45'resp'45''8776'_574 ::
  T_UltraMetric_508 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_574 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_576 ~v0 ~v1 v2
  = du_'8818''45'resp'691''45''8776'_576 v2
du_'8818''45'resp'691''45''8776'_576 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_576 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_578 ~v0 ~v1 v2
  = du_'8818''45'resp'737''45''8776'_578 v2
du_'8818''45'resp'737''45''8776'_578 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_578 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_582 ~v0 ~v1 v2
  = du_isPartialEquivalence_582 v2
du_isPartialEquivalence_582 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_582 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.refl
d_refl_584 :: T_UltraMetric_508 -> AgdaAny -> AgdaAny
d_refl_584 v0
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
                     (coe d_isUltraMetric_528 (coe v0)))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.reflexive
d_reflexive_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_586 ~v0 ~v1 v2 = du_reflexive_586 v2
du_reflexive_586 ::
  T_UltraMetric_508 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_586 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.sym
d_sym_588 ::
  T_UltraMetric_508 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_588 v0
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
                     (coe d_isUltraMetric_528 (coe v0)))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.EqC.trans
d_trans_590 ::
  T_UltraMetric_508 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_590 v0
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
                     (coe d_isUltraMetric_528 (coe v0)))))))
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_594 ~v0 ~v1 v2
  = du_isPartialEquivalence_594 v2
du_isPartialEquivalence_594 ::
  T_UltraMetric_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_594 v0
  = let v1 = d_isUltraMetric_528 (coe v0) in
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
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.refl
d_refl_596 ::
  T_UltraMetric_508 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_596 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.reflexive
d_reflexive_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_598 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.sym
d_sym_600 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_600 = erased
-- Function.Metric.Nat.Bundles.UltraMetric._.Eq.trans
d_trans_602 ::
  T_UltraMetric_508 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_602 = erased
-- Function.Metric.Nat.Bundles.UltraMetric.semiMetric
d_semiMetric_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 -> T_SemiMetric_290
d_semiMetric_604 ~v0 ~v1 v2 = du_semiMetric_604 v2
du_semiMetric_604 :: T_UltraMetric_508 -> T_SemiMetric_290
du_semiMetric_604 v0
  = coe
      C_constructor_390 (d_d_526 (coe v0))
      (MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe d_isUltraMetric_528 (coe v0)))
-- Function.Metric.Nat.Bundles.UltraMetric._.preMetric
d_preMetric_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 -> T_PreMetric_98
d_preMetric_608 ~v0 ~v1 v2 = du_preMetric_608 v2
du_preMetric_608 :: T_UltraMetric_508 -> T_PreMetric_98
du_preMetric_608 v0
  = let v1 = coe du_semiMetric_604 (coe v0) in
    coe (coe du_preMetric_278 (coe du_quasiSemiMetric_382 (coe v1)))
-- Function.Metric.Nat.Bundles.UltraMetric._.protoMetric
d_protoMetric_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 -> T_ProtoMetric_12
d_protoMetric_610 ~v0 ~v1 v2 = du_protoMetric_610 v2
du_protoMetric_610 :: T_UltraMetric_508 -> T_ProtoMetric_12
du_protoMetric_610 v0
  = let v1 = coe du_semiMetric_604 (coe v0) in
    coe
      (let v2 = coe du_quasiSemiMetric_382 (coe v1) in
       coe (coe du_protoMetric_182 (coe du_preMetric_278 (coe v2))))
-- Function.Metric.Nat.Bundles.UltraMetric._.quasiSemiMetric
d_quasiSemiMetric_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_UltraMetric_508 -> T_QuasiSemiMetric_190
d_quasiSemiMetric_612 ~v0 ~v1 v2 = du_quasiSemiMetric_612 v2
du_quasiSemiMetric_612 ::
  T_UltraMetric_508 -> T_QuasiSemiMetric_190
du_quasiSemiMetric_612 v0
  = coe du_quasiSemiMetric_382 (coe du_semiMetric_604 (coe v0))
