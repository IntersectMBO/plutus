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

module MAlonzo.Code.Function.Metric.Nat.Structures where

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

-- Function.Metric.Nat.Structures.IsProtoMetric
d_IsProtoMetric_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_IsProtoMetric_14 = erased
-- Function.Metric.Nat.Structures.IsPreMetric
d_IsPreMetric_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_IsPreMetric_18 = erased
-- Function.Metric.Nat.Structures.IsQuasiSemiMetric
d_IsQuasiSemiMetric_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_IsQuasiSemiMetric_22 = erased
-- Function.Metric.Nat.Structures.IsSemiMetric
d_IsSemiMetric_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_IsSemiMetric_26 = erased
-- Function.Metric.Nat.Structures.IsMetric
d_IsMetric_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_IsMetric_30 = erased
-- Function.Metric.Nat.Structures.IsMetric._.0⇒≈
d_0'8658''8776'_48 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_48 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe v0)))
-- Function.Metric.Nat.Structures.IsMetric._.antisym
d_antisym_50 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_50 = erased
-- Function.Metric.Nat.Structures.IsMetric._.cong
d_cong_52 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_52 = erased
-- Function.Metric.Nat.Structures.IsMetric._.isEquivalence
d_isEquivalence_54 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_54 v0
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
                        (coe v0)))))))
-- Function.Metric.Nat.Structures.IsMetric._.isPartialOrder
d_isPartialOrder_56 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_56 v0
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
                  (coe v0)))))
-- Function.Metric.Nat.Structures.IsMetric._.isPreMetric
d_isPreMetric_58 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_58 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe v0)))
-- Function.Metric.Nat.Structures.IsMetric._.isPreorder
d_isPreorder_60 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_60 v0
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
                     (coe v0))))))
-- Function.Metric.Nat.Structures.IsMetric._.isProtoMetric
d_isProtoMetric_62 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_62 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
               (coe v0))))
-- Function.Metric.Nat.Structures.IsMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_64 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_64 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe v0))
-- Function.Metric.Nat.Structures.IsMetric._.isSemiMetric
d_isSemiMetric_66 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
d_isSemiMetric_66 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350 (coe v0)
-- Function.Metric.Nat.Structures.IsMetric._.nonNegative
d_nonNegative_68 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_68 v0
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
                  (coe v0)))))
-- Function.Metric.Nat.Structures.IsMetric._.refl
d_refl_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_70 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_70 v5
du_refl_70 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_70 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.reflexive
d_reflexive_72 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_72 v0
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
                        (coe v0)))))))
-- Function.Metric.Nat.Structures.IsMetric._.sym
d_sym_74 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_74 = erased
-- Function.Metric.Nat.Structures.IsMetric._.trans
d_trans_76 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_76 v0
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
                        (coe v0)))))))
-- Function.Metric.Nat.Structures.IsMetric._.triangle
d_triangle_78 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_triangle_78 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_triangle_352 (coe v0)
-- Function.Metric.Nat.Structures.IsMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_80 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_80 v0
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
                  (coe v0)))))
-- Function.Metric.Nat.Structures.IsMetric._.≈⇒0
d_'8776''8658'0_82 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_82 = erased
-- Function.Metric.Nat.Structures.IsMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_84 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_84 v5
du_'8764''45'resp'45''8776'_84 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_84 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_86 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_86 v5
du_'8764''45'resp'691''45''8776'_86 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_86 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_88 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_88 v5
du_'8764''45'resp'737''45''8776'_88 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_88 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_90 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_90 v5
du_'8818''45'resp'45''8776'_90 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_90 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_92 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_92 v5
du_'8818''45'resp'691''45''8776'_92 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_92 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_94 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_94 v5
du_'8818''45'resp'737''45''8776'_94 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_94 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_98 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_98 v5
du_isPartialEquivalence_98 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_98 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.EqC.refl
d_refl_100 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny
d_refl_100 v0
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
                     (coe v0))))))
-- Function.Metric.Nat.Structures.IsMetric._.EqC.reflexive
d_reflexive_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_102 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_102 v5
du_reflexive_102 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_102 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.EqC.sym
d_sym_104 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_104 v0
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
                     (coe v0))))))
-- Function.Metric.Nat.Structures.IsMetric._.EqC.trans
d_trans_106 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_106 v0
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
                     (coe v0))))))
-- Function.Metric.Nat.Structures.IsMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_110 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_110 v5
du_isPartialEquivalence_110 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_110 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsMetric._.Eq.refl
d_refl_112 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_112 = erased
-- Function.Metric.Nat.Structures.IsMetric._.Eq.reflexive
d_reflexive_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_114 = erased
-- Function.Metric.Nat.Structures.IsMetric._.Eq.sym
d_sym_116 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_116 = erased
-- Function.Metric.Nat.Structures.IsMetric._.Eq.trans
d_trans_118 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_118 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric
d_IsUltraMetric_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_IsUltraMetric_120 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric._.0⇒≈
d_0'8658''8776'_138 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_0'8658''8776'_138 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_0'8658''8776'_188
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe v0)))
-- Function.Metric.Nat.Structures.IsUltraMetric._.antisym
d_antisym_140 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antisym_140 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric._.cong
d_cong_142 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_142 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric._.isEquivalence
d_isEquivalence_144 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_144 v0
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
                        (coe v0)))))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.isPartialOrder
d_isPartialOrder_146 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_146 v0
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
                  (coe v0)))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.isPreMetric
d_isPreMetric_148 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_isPreMetric_148 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
            (coe v0)))
-- Function.Metric.Nat.Structures.IsUltraMetric._.isPreorder
d_isPreorder_150 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_150 v0
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
                     (coe v0))))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.isProtoMetric
d_isProtoMetric_152 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_isProtoMetric_152 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isProtoMetric_112
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isPreMetric_186
         (coe
            MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
            (coe
               MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
               (coe v0))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.isQuasiSemiMetric
d_isQuasiSemiMetric_154 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_isQuasiSemiMetric_154 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isQuasiSemiMetric_264
      (coe
         MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
         (coe v0))
-- Function.Metric.Nat.Structures.IsUltraMetric._.isSemiMetric
d_isSemiMetric_156 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
d_isSemiMetric_156 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350 (coe v0)
-- Function.Metric.Nat.Structures.IsUltraMetric._.nonNegative
d_nonNegative_158 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nonNegative_158 v0
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
                  (coe v0)))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.refl
d_refl_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_refl_160 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_160 v5
du_refl_160 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_refl_160 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.reflexive
d_reflexive_162 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_reflexive_162 v0
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
                        (coe v0)))))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.sym
d_sym_164 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_164 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric._.trans
d_trans_166 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_trans_166 v0
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
                        (coe v0)))))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.triangle
d_triangle_168 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_triangle_168 v0
  = coe
      MAlonzo.Code.Function.Metric.Structures.d_triangle_352 (coe v0)
-- Function.Metric.Nat.Structures.IsUltraMetric._.≈-isEquivalence
d_'8776''45'isEquivalence_170 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_170 v0
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
                  (coe v0)))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.≈⇒0
d_'8776''8658'0_172 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658'0_172 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric._.∼-resp-≈
d_'8764''45'resp'45''8776'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_174 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'45''8776'_174 v5
du_'8764''45'resp'45''8776'_174 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_174 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'691''45''8776'_176 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'691''45''8776'_176 v5
du_'8764''45'resp'691''45''8776'_176 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'691''45''8776'_176 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8764''45'resp'737''45''8776'_178 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8764''45'resp'737''45''8776'_178 v5
du_'8764''45'resp'737''45''8776'_178 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8764''45'resp'737''45''8776'_178 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.≲-resp-≈
d_'8818''45'resp'45''8776'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_180 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'45''8776'_180 v5
du_'8818''45'resp'45''8776'_180 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_180 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'691''45''8776'_182 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'691''45''8776'_182 v5
du_'8818''45'resp'691''45''8776'_182 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'691''45''8776'_182 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8818''45'resp'737''45''8776'_184 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8818''45'resp'737''45''8776'_184 v5
du_'8818''45'resp'737''45''8776'_184 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8818''45'resp'737''45''8776'_184 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.EqC.isPartialEquivalence
d_isPartialEquivalence_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_188 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_188 v5
du_isPartialEquivalence_188 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_188 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.EqC.refl
d_refl_190 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny
d_refl_190 v0
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
                     (coe v0))))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.EqC.reflexive
d_reflexive_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_192 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_192 v5
du_reflexive_192 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_192 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.EqC.sym
d_sym_194 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_194 v0
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
                     (coe v0))))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.EqC.trans
d_trans_196 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_196 v0
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
                     (coe v0))))))
-- Function.Metric.Nat.Structures.IsUltraMetric._.Eq.isPartialEquivalence
d_isPartialEquivalence_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_200 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_200 v5
du_isPartialEquivalence_200 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_200 v0
  = let v1
          = MAlonzo.Code.Function.Metric.Structures.d_isSemiMetric_350
              (coe v0) in
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
-- Function.Metric.Nat.Structures.IsUltraMetric._.Eq.refl
d_refl_202 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_202 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric._.Eq.reflexive
d_reflexive_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> Integer) ->
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_204 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric._.Eq.sym
d_sym_206 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_206 = erased
-- Function.Metric.Nat.Structures.IsUltraMetric._.Eq.trans
d_trans_208 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_208 = erased
