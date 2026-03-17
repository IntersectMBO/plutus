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

module MAlonzo.Code.Algebra.Properties.Monoid.Mult where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Definitions.RawMonoid
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Properties.Monoid.Mult._._IdempotentOn_
d__IdempotentOn__122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d__IdempotentOn__122 = erased
-- Algebra.Properties.Monoid.Mult._._×_
d__'215'__244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  Integer -> AgdaAny -> AgdaAny
d__'215'__244 ~v0 ~v1 v2 = du__'215'__244 v2
du__'215'__244 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  Integer -> AgdaAny -> AgdaAny
du__'215'__244 v0
  = coe
      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
-- Algebra.Properties.Monoid.Mult.×-congʳ
d_'215''45'cong'691'_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'215''45'cong'691'_250 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'215''45'cong'691'_250 v2 v3 v4 v5 v6
du_'215''45'cong'691'_250 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'215''45'cong'691'_250 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)))))
             (coe
                MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                   (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                   (coe (0 :: Integer)))
                (\ v5 v6 -> v5) v2 v3)
      _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0))))
                v2 v3
                (coe
                   MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                      (coe v5))
                   (\ v6 v7 -> v6) v2 v3)
                (coe
                   MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                   (\ v6 v7 -> v7)
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                      (coe v5))
                   v2 v3)
                v4
                (coe
                   du_'215''45'cong'691'_250 (coe v0) (coe v5) (coe v2) (coe v3)
                   (coe v4)))
-- Algebra.Properties.Monoid.Mult.×-cong
d_'215''45'cong_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_'215''45'cong_258 ~v0 ~v1 v2 v3 ~v4 v5 v6 ~v7 v8
  = du_'215''45'cong_258 v2 v3 v5 v6 v8
du_'215''45'cong_258 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'215''45'cong_258 v0 v1 v2 v3 v4
  = coe
      du_'215''45'cong'691'_250 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
-- Algebra.Properties.Monoid.Mult.×-congˡ
d_'215''45'cong'737'_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'215''45'cong'737'_268 ~v0 ~v1 v2 v3 v4 ~v5 ~v6
  = du_'215''45'cong'737'_268 v2 v3 v4
du_'215''45'cong'737'_268 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  AgdaAny -> Integer -> AgdaAny
du_'215''45'cong'737'_268 v0 v1 v2
  = coe
      du_'215''45'cong_258 (coe v0) (coe v2) (coe v1) (coe v1)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)))))
         v1)
-- Algebra.Properties.Monoid.Mult.×-homo-0
d_'215''45'homo'45'0_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 -> AgdaAny -> AgdaAny
d_'215''45'homo'45'0_274 ~v0 ~v1 v2 v3
  = du_'215''45'homo'45'0_274 v2 v3
du_'215''45'homo'45'0_274 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 -> AgdaAny -> AgdaAny
du_'215''45'homo'45'0_274 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
         (coe (0 :: Integer)) (coe v1))
-- Algebra.Properties.Monoid.Mult.×-homo-1
d_'215''45'homo'45'1_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 -> AgdaAny -> AgdaAny
d_'215''45'homo'45'1_280 ~v0 ~v1 v2 = du_'215''45'homo'45'1_280 v2
du_'215''45'homo'45'1_280 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 -> AgdaAny -> AgdaAny
du_'215''45'homo'45'1_280 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'691'_726
      (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0))
-- Algebra.Properties.Monoid.Mult.×-homo-+
d_'215''45'homo'45''43'_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  AgdaAny -> Integer -> Integer -> AgdaAny
d_'215''45'homo'45''43'_288 ~v0 ~v1 v2 v3 v4 v5
  = du_'215''45'homo'45''43'_288 v2 v3 v4 v5
du_'215''45'homo'45''43'_288 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  AgdaAny -> Integer -> Integer -> AgdaAny
du_'215''45'homo'45''43'_288 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_sym_36
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)))))
             (coe
                MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                (MAlonzo.Code.Algebra.Bundles.d_ε_908 (coe v0))
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                   (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                   (coe v3) (coe v1)))
             (coe
                MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                (coe v3) (coe v1))
             (coe
                MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                (MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0))
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                   (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                   (coe v3) (coe v1)))
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (\ v5 v6 v7 ->
                   coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
                (coe
                   MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                      (coe addInt (coe v4) (coe v3)) (coe v1)))
                (coe
                   MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                   (coe
                      MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe v4) (coe v1)))
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                      (coe v3) (coe v1)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v5 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                             coe
                               (let v6
                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                          (coe v5) in
                                coe
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                        (coe v6))))))))
                   (coe
                      MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe addInt (coe v4) (coe v3)) (coe v1)))
                   (coe
                      MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                      (coe
                         MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v4) (coe v1))
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v3) (coe v1))))
                   (coe
                      MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                      (coe
                         MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v4) (coe v1)))
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe v3) (coe v1)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                               (let v5 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                                coe
                                  (let v6
                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                             (coe v5) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                        (coe
                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                           (coe v6))))))))
                      (coe
                         MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                         (coe
                            MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                            (coe
                               MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                               (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                               (coe v4) (coe v1))
                            (coe
                               MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                               (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                               (coe v3) (coe v1))))
                      (coe
                         MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                         (coe
                            MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                            (coe
                               MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                               (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                               (coe v4) (coe v1)))
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v3) (coe v1)))
                      (coe
                         MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                         (coe
                            MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                            (coe
                               MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                               (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                               (coe v4) (coe v1)))
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v3) (coe v1)))
                      (let v5
                             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v5
                                           = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                                     coe
                                       (let v6
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v5) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v6)))))) in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v5))
                            (coe
                               MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                               (coe
                                  MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                                  (coe
                                     MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                     (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                     (coe v4) (coe v1)))
                               (coe
                                  MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                  (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                  (coe v3) (coe v1)))))
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                  (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)))))
                         (coe
                            MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                            (coe
                               MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                               (coe
                                  MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                  (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                  (coe v4) (coe v1)))
                            (coe
                               MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                               (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                               (coe v3) (coe v1)))
                         (coe
                            MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                            (coe
                               MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                               (coe
                                  MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                  (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                  (coe v4) (coe v1))
                               (coe
                                  MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                  (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                  (coe v3) (coe v1))))
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_assoc_480
                            (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                               (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)))
                            v1
                            (coe
                               MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                               (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                               (coe v4) (coe v1))
                            (coe
                               MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                               (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                               (coe v3) (coe v1)))))
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                      (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                            (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0))))
                      v1 v1
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe addInt (coe v4) (coe v3)) (coe v1))
                      (coe
                         MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v4) (coe v1))
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v3) (coe v1)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                  (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)))))
                         v1)
                      (coe
                         du_'215''45'homo'45''43'_288 (coe v0) (coe v1) (coe v4)
                         (coe v3)))))
-- Algebra.Properties.Monoid.Mult.×-idem
d_'215''45'idem_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  AgdaAny ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> AgdaAny
d_'215''45'idem_306 ~v0 ~v1 v2 v3 v4 v5 ~v6
  = du_'215''45'idem_306 v2 v3 v4 v5
du_'215''45'idem_306 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  AgdaAny -> AgdaAny -> Integer -> AgdaAny
du_'215''45'idem_306 v0 v1 v2 v3
  = case coe v3 of
      1 -> coe
             MAlonzo.Code.Algebra.Structures.du_identity'691'_726
             (MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)) v1
      _ -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v4 v5 v6 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
             (coe
                MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                   (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                   (coe subInt (coe v3) (coe (1 :: Integer))) (coe v1)))
             v1
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                      (coe
                         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                         (let v4 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                          coe
                            (let v5
                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v4) in
                             coe
                               (coe
                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v5))))))))
                (coe
                   MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                      (coe subInt (coe v3) (coe (1 :: Integer))) (coe v1)))
                (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1 v1) v1
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v4 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                             coe
                               (let v5
                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                          (coe v4) in
                                coe
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                        (coe v5))))))))
                   (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0 v1 v1) v1 v1
                   (let v4
                          = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v4 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                                  coe
                                    (let v5
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v4) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v5)))))) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                            (coe v4))
                         (coe v1)))
                   v2)
                (let v4 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                 coe
                   (let v5
                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v4) in
                    coe
                      (let v6 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v5) in
                       coe
                         (let v7
                                = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v6) in
                          coe
                            (let v8
                                   = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                       (coe v6) in
                             coe
                               (coe
                                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                  v8
                                  (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                        (coe v7)))
                                  v1
                                  (coe
                                     MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                     (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                     (coe subInt (coe v3) (coe (1 :: Integer))) (coe v1))
                                  v1
                                  (coe
                                     du_'215''45'idem_306 (coe v0) (coe v1) (coe v2)
                                     (coe subInt (coe v3) (coe (1 :: Integer)))))))))))
-- Algebra.Properties.Monoid.Mult.×-assocˡ
d_'215''45'assoc'737'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  AgdaAny -> Integer -> Integer -> AgdaAny
d_'215''45'assoc'737'_324 ~v0 ~v1 v2 v3 v4 v5
  = du_'215''45'assoc'737'_324 v2 v3 v4 v5
du_'215''45'assoc'737'_324 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886 ->
  AgdaAny -> Integer -> Integer -> AgdaAny
du_'215''45'assoc'737'_324 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0)))))
             (coe
                MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                   (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                   (coe v3) (coe v1)))
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (\ v5 v6 v7 ->
                   coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
                (coe
                   MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                      (coe v3) (coe v1))
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                      (coe v4)
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe v3) (coe v1))))
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                   (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                   (coe mulInt (coe v2) (coe v3)) (coe v1))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v5 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                             coe
                               (let v6
                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                          (coe v5) in
                                coe
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                        (coe v6))))))))
                   (coe
                      MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe v3) (coe v1))
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe v4)
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v3) (coe v1))))
                   (coe
                      MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe v3) (coe v1))
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe mulInt (coe v4) (coe v3)) (coe v1)))
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                      (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                      (coe mulInt (coe v2) (coe v3)) (coe v1))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                               (let v5 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                                coe
                                  (let v6
                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                             (coe v5) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                        (coe
                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                           (coe v6))))))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v5 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                             coe
                               (let v6
                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                          (coe v5) in
                                coe
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6)))))))
                      (coe
                         MAlonzo.Code.Algebra.Bundles.d__'8729'__906 v0
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe v3) (coe v1))
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                            (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                            (coe mulInt (coe v4) (coe v3)) (coe v1)))
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe mulInt (coe v2) (coe v3)) (coe v1))
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                         (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                         (coe mulInt (coe v2) (coe v3)) (coe v1))
                      (let v5
                             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v5
                                           = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                                     coe
                                       (let v6
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v5) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v6)))))) in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v5))
                            (coe
                               MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                               (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                               (coe mulInt (coe v2) (coe v3)) (coe v1))))
                      (coe
                         du_'215''45'homo'45''43'_288 (coe v0) (coe v1) (coe v3)
                         (coe mulInt (coe v4) (coe v3))))
                   (let v5 = MAlonzo.Code.Algebra.Bundles.d_isMonoid_910 (coe v0) in
                    coe
                      (let v6
                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                       coe
                         (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                          coe
                            (let v8
                                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                             coe
                               (let v9
                                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                          (coe v7) in
                                coe
                                  (coe
                                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                     v9
                                     (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (coe v8)))
                                     (coe
                                        MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                        (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                        (coe v3) (coe v1))
                                     (coe
                                        MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                        (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                           (coe
                                              MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958
                                              (coe v0))
                                           (coe v3) (coe v1)))
                                     (coe
                                        MAlonzo.Code.Algebra.Definitions.RawMonoid.du__'215'__64
                                        (coe MAlonzo.Code.Algebra.Bundles.du_rawMonoid_958 (coe v0))
                                        (coe mulInt (coe v4) (coe v3)) (coe v1))
                                     (coe
                                        du_'215''45'assoc'737'_324 (coe v0) (coe v1) (coe v4)
                                        (coe v3))))))))))
