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

module MAlonzo.Code.Algebra.Properties.RingWithoutOne where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Properties.AbelianGroup
import qualified MAlonzo.Code.Algebra.Properties.Group
import qualified MAlonzo.Code.Algebra.Properties.Loop
import qualified MAlonzo.Code.Algebra.Properties.QQuasigroup
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Properties.RingWithoutOne._._//_
d__'47''47'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__18 ~v0 ~v1 v2 = du__'47''47'__18 v2
du__'47''47'__18 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__18 v0
  = let v1 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v1)
            (coe v2)))
-- Algebra.Properties.RingWithoutOne._.cancel
d_cancel_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_184 ~v0 ~v1 v2 = du_cancel_184 v2
du_cancel_184 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_184 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel_308
            (coe
               MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564 (coe v2))))
-- Algebra.Properties.RingWithoutOne._.cancelʳ
d_cancel'691'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_186 ~v0 ~v1 v2 = du_cancel'691'_186 v2
du_cancel'691'_186 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_186 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'691'_298
            (coe
               MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564 (coe v2))))
-- Algebra.Properties.RingWithoutOne._.cancelˡ
d_cancel'737'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_188 ~v0 ~v1 v2 = du_cancel'737'_188 v2
du_cancel'737'_188 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_188 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'737'_288
            (coe
               MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564 (coe v2))))
-- Algebra.Properties.RingWithoutOne._.identity-unique
d_identity'45'unique_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_identity'45'unique_190 ~v0 ~v1 v2 = du_identity'45'unique_190 v2
du_identity'45'unique_190 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_identity'45'unique_190 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Loop.du_identity'45'unique_326
            (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_580 (coe v2))))
-- Algebra.Properties.RingWithoutOne._.identityʳ-unique
d_identity'691''45'unique_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'691''45'unique_192 ~v0 ~v1 v2
  = du_identity'691''45'unique_192 v2
du_identity'691''45'unique_192 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_identity'691''45'unique_192 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Loop.du_identity'691''45'unique_316
            (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_580 (coe v2))))
-- Algebra.Properties.RingWithoutOne._.identityˡ-unique
d_identity'737''45'unique_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'737''45'unique_194 ~v0 ~v1 v2
  = du_identity'737''45'unique_194 v2
du_identity'737''45'unique_194 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_identity'737''45'unique_194 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Loop.du_identity'737''45'unique_304
            (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_580 (coe v2))))
-- Algebra.Properties.RingWithoutOne._.inverseʳ-unique
d_inverse'691''45'unique_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691''45'unique_196 ~v0 ~v1 v2
  = du_inverse'691''45'unique_196 v2
du_inverse'691''45'unique_196 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691''45'unique_196 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_inverse'691''45'unique_606
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.inverseˡ-unique
d_inverse'737''45'unique_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737''45'unique_198 ~v0 ~v1 v2
  = du_inverse'737''45'unique_198 v2
du_inverse'737''45'unique_198 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'737''45'unique_198 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_inverse'737''45'unique_594
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.ε⁻¹≈ε
d_ε'8315''185''8776'ε_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 -> AgdaAny
d_ε'8315''185''8776'ε_200 ~v0 ~v1 v2
  = du_ε'8315''185''8776'ε_200 v2
du_ε'8315''185''8776'ε_200 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 -> AgdaAny
du_ε'8315''185''8776'ε_200 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_ε'8315''185''8776'ε_614
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.⁻¹-∙-comm
d_'8315''185''45''8729''45'comm_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45''8729''45'comm_202 ~v0 ~v1 v2
  = du_'8315''185''45''8729''45'comm_202 v2
du_'8315''185''45''8729''45'comm_202 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45''8729''45'comm_202 v0
  = coe
      MAlonzo.Code.Algebra.Properties.AbelianGroup.du_'8315''185''45''8729''45'comm_244
      (coe
         MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506 (coe v0))
-- Algebra.Properties.RingWithoutOne._.⁻¹-anti-homo-∙
d_'8315''185''45'anti'45'homo'45''8729'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''8729'_204 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''8729'_204 v2
du_'8315''185''45'anti'45'homo'45''8729'_204 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''8729'_204 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''8729'_656
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.⁻¹-injective
d_'8315''185''45'injective_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'injective_206 ~v0 ~v1 v2
  = du_'8315''185''45'injective_206 v2
du_'8315''185''45'injective_206 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'injective_206 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'injective_650
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.⁻¹-involutive
d_'8315''185''45'involutive_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny
d_'8315''185''45'involutive_208 ~v0 ~v1 v2
  = du_'8315''185''45'involutive_208 v2
du_'8315''185''45'involutive_208 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny
du_'8315''185''45'involutive_208 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'involutive_624
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.//-cong₂
d_'47''47''45'cong'8322'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'8322'_210 ~v0 ~v1 v2
  = du_'47''47''45'cong'8322'_210 v2
du_'47''47''45'cong'8322'_210 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'8322'_210 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'cong'8322'_528
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.//-rightDivides
d_'47''47''45'rightDivides_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'47''47''45'rightDivides_212 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides_212 v2
du_'47''47''45'rightDivides_212 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'47''47''45'rightDivides_212 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides_560
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.//-rightDividesʳ
d_'47''47''45'rightDivides'691'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'rightDivides'691'_214 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides'691'_214 v2
du_'47''47''45'rightDivides'691'_214 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'rightDivides'691'_214 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides'691'_554
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.//-rightDividesˡ
d_'47''47''45'rightDivides'737'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'rightDivides'737'_216 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides'737'_216 v2
du_'47''47''45'rightDivides'737'_216 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'rightDivides'737'_216 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides'737'_548
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.\\-cong₂
d_'92''92''45'cong'8322'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'8322'_218 ~v0 ~v1 v2
  = du_'92''92''45'cong'8322'_218 v2
du_'92''92''45'cong'8322'_218 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'8322'_218 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'cong'8322'_522
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.\\-leftDivides
d_'92''92''45'leftDivides_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'92''92''45'leftDivides_220 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides_220 v2
du_'92''92''45'leftDivides_220 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'92''92''45'leftDivides_220 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides_546
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.\\-leftDividesʳ
d_'92''92''45'leftDivides'691'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'leftDivides'691'_222 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides'691'_222 v2
du_'92''92''45'leftDivides'691'_222 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'leftDivides'691'_222 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides'691'_540
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.\\-leftDividesˡ
d_'92''92''45'leftDivides'737'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'leftDivides'737'_224 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides'737'_224 v2
du_'92''92''45'leftDivides'737'_224 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'leftDivides'737'_224 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides'737'_534
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.\\≗flip-//⇒comm
d_'92''92''8791'flip'45''47''47''8658'comm_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''8791'flip'45''47''47''8658'comm_226 ~v0 ~v1 v2
  = du_'92''92''8791'flip'45''47''47''8658'comm_226 v2
du_'92''92''8791'flip'45''47''47''8658'comm_226 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''8791'flip'45''47''47''8658'comm_226 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'92''92''8791'flip'45''47''47''8658'comm_686
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.comm⇒\\≗flip-//
d_comm'8658''92''92''8791'flip'45''47''47'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm'8658''92''92''8791'flip'45''47''47'_228 ~v0 ~v1 v2
  = du_comm'8658''92''92''8791'flip'45''47''47'_228 v2
du_comm'8658''92''92''8791'flip'45''47''47'_228 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm'8658''92''92''8791'flip'45''47''47'_228 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_comm'8658''92''92''8791'flip'45''47''47'_698
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.isLoop
d_isLoop_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3046
d_isLoop_230 ~v0 ~v1 v2 = du_isLoop_230 v2
du_isLoop_230 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3046
du_isLoop_230 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_isLoop_578
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.isQuasigroup
d_isQuasigroup_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2964
d_isQuasigroup_232 ~v0 ~v1 v2 = du_isQuasigroup_232 v2
du_isQuasigroup_232 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2964
du_isQuasigroup_232 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_isQuasigroup_562
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.loop
d_loop_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Algebra.Bundles.T_Loop_4384
d_loop_234 ~v0 ~v1 v2 = du_loop_234 v2
du_loop_234 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Algebra.Bundles.T_Loop_4384
du_loop_234 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_loop_580
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.quasigroup
d_quasigroup_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4284
d_quasigroup_236 ~v0 ~v1 v2 = du_quasigroup_236 v2
du_quasigroup_236 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4284
du_quasigroup_236 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.xyx⁻¹≈y
d_xyx'8315''185''8776'y_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_xyx'8315''185''8776'y_238 ~v0 ~v1 v2
  = du_xyx'8315''185''8776'y_238 v2
du_xyx'8315''185''8776'y_238 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_xyx'8315''185''8776'y_238 v0
  = coe
      MAlonzo.Code.Algebra.Properties.AbelianGroup.du_xyx'8315''185''8776'y_234
      (coe
         MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506 (coe v0))
-- Algebra.Properties.RingWithoutOne._.x∙y⁻¹≈ε⇒x≈y
d_x'8729'y'8315''185''8776'ε'8658'x'8776'y_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'y'8315''185''8776'ε'8658'x'8776'y_240 ~v0 ~v1 v2
  = du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_240 v2
du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_240 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_240 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_630
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.x≈y⇒x∙y⁻¹≈ε
d_x'8776'y'8658'x'8729'y'8315''185''8776'ε_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'y'8658'x'8729'y'8315''185''8776'ε_242 ~v0 ~v1 v2
  = du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_242 v2
du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_242 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_242 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_642
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.x≈z//y
d_x'8776'z'47''47'y_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'z'47''47'y_244 ~v0 ~v1 v2 = du_x'8776'z'47''47'y_244 v2
du_x'8776'z'47''47'y_244 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'z'47''47'y_244 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.QQuasigroup.du_x'8776'z'47''47'y_278
            (coe
               MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564 (coe v2))))
-- Algebra.Properties.RingWithoutOne._.y≈x\\z
d_y'8776'x'92''92'z_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8776'x'92''92'z_246 ~v0 ~v1 v2 = du_y'8776'x'92''92'z_246 v2
du_y'8776'x'92''92'z_246 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8776'x'92''92'z_246 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.QQuasigroup.du_y'8776'x'92''92'z_262
            (coe
               MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564 (coe v2))))
-- Algebra.Properties.RingWithoutOne._.⁻¹-anti-homo-//
d_'8315''185''45'anti'45'homo'45''47''47'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''47''47'_248 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''47''47'_248 v2
du_'8315''185''45'anti'45'homo'45''47''47'_248 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''47''47'_248 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''47''47'_666
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.⁻¹-anti-homo-\\
d_'8315''185''45'anti'45'homo'45''92''92'_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''92''92'_250 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''92''92'_250 v2
du_'8315''185''45'anti'45'homo'45''92''92'_250 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''92''92'_250 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''92''92'_676
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne._.⁻¹-anti-homo‿-
d_'8315''185''45'anti'45'homo'8255''45'_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'8255''45'_252 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'8255''45'_252 v2
du_'8315''185''45'anti'45'homo'8255''45'_252 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'8255''45'_252 v0
  = coe
      MAlonzo.Code.Algebra.Properties.AbelianGroup.du_'8315''185''45'anti'45'homo'8255''45'_228
      (coe
         MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506 (coe v0))
-- Algebra.Properties.RingWithoutOne._.⁻¹-selfInverse
d_'8315''185''45'selfInverse_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'selfInverse_254 ~v0 ~v1 v2
  = du_'8315''185''45'selfInverse_254 v2
du_'8315''185''45'selfInverse_254 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'selfInverse_254 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'selfInverse_616
         (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v1)))
-- Algebra.Properties.RingWithoutOne.-‿distribˡ-*
d_'45''8255'distrib'737''45''42'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'distrib'737''45''42'_260 ~v0 ~v1 v2 v3 v4
  = du_'45''8255'distrib'737''45''42'_260 v2 v3 v4
du_'45''8255'distrib'737''45''42'_260 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255'distrib'737''45''42'_260 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                           (coe v0))))))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
         (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
      (coe
         MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
            (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
         (coe
            MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe v6) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                          (coe v7)))))))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                       (coe v7))))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
               (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
               (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0)))
            (coe
               MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                      (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                            (coe v5) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v6) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v7)))))))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe v6) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                          (coe v7))))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
                  (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                         (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                                  coe
                                    (let v6
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                               (coe v5) in
                                     coe
                                       (let v7
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v6) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v7)))))))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                      (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                            (coe v5) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v6) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v7))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v3
                                     = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                         (coe v0) in
                               coe
                                 (let v4
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                            (coe v3) in
                                  coe
                                    (let v5
                                           = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                               (coe v4) in
                                     coe
                                       (let v6
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                  (coe v5) in
                                        coe
                                          (let v7
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v6) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v7)))))))))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                         (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                                  coe
                                    (let v6
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                               (coe v5) in
                                     coe
                                       (let v7
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v6) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v7))))))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v1)
                           v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v3
                                        = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                            (coe v0) in
                                  coe
                                    (let v4
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                               (coe v3) in
                                     coe
                                       (let v5
                                              = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                  (coe v4) in
                                        coe
                                          (let v6
                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                     (coe v5) in
                                           coe
                                             (let v7
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                        (coe v6) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                      (coe v7)))))))))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v1)
                              v2)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                              (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0)) v2)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v3
                                           = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                               (coe v0) in
                                     coe
                                       (let v4
                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                  (coe v3) in
                                        coe
                                          (let v5
                                                 = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                     (coe v4) in
                                           coe
                                             (let v6
                                                    = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                        (coe v5) in
                                              coe
                                                (let v7
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                           (coe v6) in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                         (coe v7)))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                 (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0)) v2)
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                              (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0))
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v3
                                              = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                  (coe v0) in
                                        coe
                                          (let v4
                                                 = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                     (coe v3) in
                                           coe
                                             (let v5
                                                    = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                        (coe v4) in
                                              coe
                                                (let v6
                                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                           (coe v5) in
                                                 coe
                                                   (let v7
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                              (coe v6) in
                                                    coe
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                            (coe v7)))))))))))
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                 (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0))
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                    (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)))
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                              (let v3
                                     = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                            (let v3
                                                   = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                       (coe v0) in
                                             coe
                                               (let v4
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                          (coe v3) in
                                                coe
                                                  (let v5
                                                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                             (coe v4) in
                                                   coe
                                                     (let v6
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                                (coe v5) in
                                                      coe
                                                        (let v7
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v6) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v7))))))))) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                       (coe v3))
                                    (coe
                                       MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                       (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))))
                              (let v3
                                     = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                         (coe v0) in
                               coe
                                 (let v4
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                            (coe v3) in
                                  coe
                                    (let v5
                                           = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                               (coe v4) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                                          (MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5))
                                          (coe
                                             MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                v2)))))))
                           (let v3
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                         (coe v0)) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                            (coe v4) in
                                  coe
                                    (let v6
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v5) in
                                     coe
                                       (let v7
                                              = MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                  (coe v6) in
                                        coe
                                          (let v8
                                                 = coe
                                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                     (coe v7) in
                                           coe
                                             (let v9
                                                    = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                        (coe v7) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                                   v9
                                                   (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                      (coe
                                                         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                         (coe v8)))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                      (coe
                                                         MAlonzo.Code.Algebra.Bundles.d__'42'__3396
                                                         v0 v1 v2))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                                      (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                         (coe v0))
                                                      v2)
                                                   (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                      (coe v0))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.du_zero'737'_2400
                                                      (MAlonzo.Code.Algebra.Bundles.d__'43'__3394
                                                         (coe v0))
                                                      (MAlonzo.Code.Algebra.Bundles.d__'42'__3396
                                                         (coe v0))
                                                      (MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                         (coe v0))
                                                      (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                         (coe v0))
                                                      (MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                         (coe v0))
                                                      v2))))))))))
                        (let v3
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe
                                      MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                      (coe v0)) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe v5) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                               (coe v6) in
                                     coe
                                       (let v8
                                              = coe
                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                  (coe v7) in
                                        coe
                                          (let v9
                                                 = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                     (coe v7) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                                v9
                                                (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                      (coe v8)))
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                                      v1 v2))
                                                (coe
                                                   MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                   (\ v10 ->
                                                      coe
                                                        MAlonzo.Code.Algebra.Bundles.d__'42'__3396
                                                        v0 v10 v2)
                                                   (\ v10 v11 -> v10)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                                      (coe
                                                         MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                         v0 v1)
                                                      v1)
                                                   (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                      (coe v0)))
                                                (coe
                                                   MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                   (\ v10 v11 -> v11)
                                                   (\ v10 ->
                                                      coe
                                                        MAlonzo.Code.Algebra.Bundles.d__'42'__3396
                                                        v0 v10 v2)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                                      (coe
                                                         MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                         v0 v1)
                                                      v1)
                                                   (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                      (coe v0)))
                                                (let v10
                                                       = coe
                                                           MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d__'43'__3394
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d__'42'__3396
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                              (coe v0)) in
                                                 coe
                                                   (let v11
                                                          = coe
                                                              MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                                                              (coe v10) in
                                                    coe
                                                      (let v12
                                                             = coe
                                                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                 (coe v11) in
                                                       coe
                                                         (let v13
                                                                = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                                    (coe v11) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                                               v13
                                                               (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                     (coe v12)))
                                                               v2
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Bundles.d__'43'__3394
                                                                  v0
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                                     v0 v1)
                                                                  v1)
                                                               (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                                  (coe v0))
                                                               (let v14
                                                                      = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                                             (coe v14) in
                                                                   coe
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.du_inverse'737'_1104
                                                                        (MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                                           (coe v15))
                                                                        v1)))))))))))))))))
                     (let v3
                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                (coe
                                   MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0)) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                               coe
                                 (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                                  coe
                                    (let v8
                                           = coe
                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                               (coe v7) in
                                     coe
                                       (let v9
                                              = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                  (coe v7) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                             v9
                                             (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                   (coe v8)))
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                   v2))
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                      v1)
                                                   v1)
                                                v2)
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                      v1)
                                                   v2)
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                   v2))
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_distrib'691'_2398
                                                (MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                   (coe v0))
                                                v2
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1)
                                                v1))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_assoc_480
                     (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                    (coe v0))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))))
               (let v3
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe
                             MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0)) in
                coe
                  (let v4
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
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
                                          MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                          (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                          (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                                          (coe
                                             MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                v2)))
                                       (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0))
                                       (let v10
                                              = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                  (coe v0) in
                                        coe
                                          (let v11
                                                 = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                     (coe v10) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_inverse'691'_1106
                                                (MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                   (coe v11))
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                   v2)))))))))))))
            (let v3
                   = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                        (MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v1) v2)))))))
-- Algebra.Properties.RingWithoutOne.-‿distribʳ-*
d_'45''8255'distrib'691''45''42'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'distrib'691''45''42'_270 ~v0 ~v1 v2 v3 v4
  = du_'45''8255'distrib'691''45''42'_270 v2 v3 v4
du_'45''8255'distrib'691''45''42'_270 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255'distrib'691''45''42'_270 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                           (coe v0))))))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))
      (coe
         MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))
         (coe
            MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe v6) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                          (coe v7)))))))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                       (coe v7))))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
               (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                  (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                      (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                            (coe v5) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v6) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe v7)))))))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe v6) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                          (coe v7))))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                  (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                     (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                     (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                         (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                                  coe
                                    (let v6
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                               (coe v5) in
                                     coe
                                       (let v7
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v6) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v7)))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                        (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                           (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v3
                                     = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                         (coe v0) in
                               coe
                                 (let v4
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                            (coe v3) in
                                  coe
                                    (let v5
                                           = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                               (coe v4) in
                                     coe
                                       (let v6
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                  (coe v5) in
                                        coe
                                          (let v7
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v6) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v7)))))))))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                         (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                                  coe
                                    (let v6
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                               (coe v5) in
                                     coe
                                       (let v7
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v6) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v7))))))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                              (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0 v2
                              (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v3
                                        = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                            (coe v0) in
                                  coe
                                    (let v4
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                               (coe v3) in
                                     coe
                                       (let v5
                                              = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                  (coe v4) in
                                        coe
                                          (let v6
                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                     (coe v5) in
                                           coe
                                             (let v7
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                        (coe v6) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                      (coe v7)))))))))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0 v2
                                 (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                              (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v3
                                           = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                               (coe v0) in
                                     coe
                                       (let v4
                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                  (coe v3) in
                                        coe
                                          (let v5
                                                 = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                     (coe v4) in
                                           coe
                                             (let v6
                                                    = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                        (coe v5) in
                                              coe
                                                (let v7
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                           (coe v6) in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                         (coe v7)))))))))))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                 (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                              (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0)))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                              (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v3
                                              = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                  (coe v0) in
                                        coe
                                          (let v4
                                                 = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                     (coe v3) in
                                           coe
                                             (let v5
                                                    = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                        (coe v4) in
                                              coe
                                                (let v6
                                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                           (coe v5) in
                                                 coe
                                                   (let v7
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                              (coe v6) in
                                                    coe
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                            (coe v7)))))))))))
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                    (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                                 (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0)))
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                              (coe
                                 MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                 (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                              (let v3
                                     = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                            (let v3
                                                   = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                       (coe v0) in
                                             coe
                                               (let v4
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                          (coe v3) in
                                                coe
                                                  (let v5
                                                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                             (coe v4) in
                                                   coe
                                                     (let v6
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                                (coe v5) in
                                                      coe
                                                        (let v7
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v6) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v7))))))))) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                       (coe v3))
                                    (coe
                                       MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                       (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))))
                              (let v3
                                     = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                         (coe v0) in
                               coe
                                 (let v4
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                            (coe v3) in
                                  coe
                                    (let v5
                                           = MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                               (coe v4) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                                          (MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5))
                                          (coe
                                             MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                v2)))))))
                           (let v3
                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                         (coe v0)) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                            (coe v4) in
                                  coe
                                    (let v6
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe v5) in
                                     coe
                                       (let v7
                                              = MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                  (coe v6) in
                                        coe
                                          (let v8
                                                 = coe
                                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                     (coe v7) in
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
                                                      MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                      (coe
                                                         MAlonzo.Code.Algebra.Bundles.d__'42'__3396
                                                         v0 v1 v2))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                                      v1
                                                      (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                         (coe v0)))
                                                   (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                      (coe v0))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.du_zero'691'_2402
                                                      (MAlonzo.Code.Algebra.Bundles.d__'43'__3394
                                                         (coe v0))
                                                      (MAlonzo.Code.Algebra.Bundles.d__'42'__3396
                                                         (coe v0))
                                                      (MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                         (coe v0))
                                                      (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                         (coe v0))
                                                      (MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                         (coe v0))
                                                      v1))))))))))
                        (let v3
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe
                                      MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                      (coe v0)) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe v5) in
                                  coe
                                    (let v7
                                           = MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                               (coe v6) in
                                     coe
                                       (let v8
                                              = coe
                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                  (coe v7) in
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
                                                   MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                                      v1 v2))
                                                (coe
                                                   MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                                      v1)
                                                   (\ v10 v11 -> v10)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                                      v2
                                                      (coe
                                                         MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                         v0 v2))
                                                   (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                      (coe v0)))
                                                (coe
                                                   MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                   (\ v10 v11 -> v11)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                                      v1)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                                      v2
                                                      (coe
                                                         MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                         v0 v2))
                                                   (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                      (coe v0)))
                                                (let v10
                                                       = coe
                                                           MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d__'43'__3394
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d__'42'__3396
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                              (coe v0)) in
                                                 coe
                                                   (let v11
                                                          = coe
                                                              MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                                                              (coe v10) in
                                                    coe
                                                      (let v12
                                                             = coe
                                                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                 (coe v11) in
                                                       coe
                                                         (let v13
                                                                = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                                    (coe v11) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                                               v13
                                                               (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                     (coe v12)))
                                                               v1
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Bundles.d__'43'__3394
                                                                  v0 v2
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Bundles.d_'45'__3398
                                                                     v0 v2))
                                                               (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400
                                                                  (coe v0))
                                                               (let v14
                                                                      = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                                             (coe v14) in
                                                                   coe
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.du_inverse'691'_1106
                                                                        (MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                                           (coe v15))
                                                                        v2)))))))))))))))))
                     (let v3
                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                (coe
                                   MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0)) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                               coe
                                 (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                                  coe
                                    (let v8
                                           = coe
                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                               (coe v7) in
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
                                                MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                   v2))
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0 v2
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                      v2)))
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                   v2)
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                   (coe
                                                      MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                      v2)))
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_distrib'737'_2396
                                                (MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                   (coe v0))
                                                v1 v2
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                                   v2)))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_assoc_480
                     (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                    (coe v0))))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                        (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                        (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))))
               (let v3
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe
                             MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0)) in
                coe
                  (let v4
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
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
                                       MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                       v9
                                       (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (coe v8)))
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                          (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                v2))
                                          (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2))
                                       (MAlonzo.Code.Algebra.Bundles.d_0'35'_3400 (coe v0))
                                       (let v10
                                              = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                  (coe v0) in
                                        coe
                                          (let v11
                                                 = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                     (coe v10) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_inverse'737'_1104
                                                (MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                   (coe v11))
                                                (coe
                                                   MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                   v2)))))))))))))
            (let v3
                   = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                        (MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                           (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v2))))))))
-- Algebra.Properties.RingWithoutOne.x+x≈x⇒x≈0
d_x'43'x'8776'x'8658'x'8776'0_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'43'x'8776'x'8658'x'8776'0_278 ~v0 ~v1 v2 v3 v4
  = du_x'43'x'8776'x'8658'x'8776'0_278 v2 v3 v4
du_x'43'x'8776'x'8658'x'8776'0_278 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'43'x'8776'x'8658'x'8776'0_278 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Algebra.Bundles.du_group_1736
              (coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v0)) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Loop.du_identity'737''45'unique_304
         (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_580 (coe v3))
         (coe v1) (coe v1) (coe v2))
-- Algebra.Properties.RingWithoutOne.x[y-z]≈xy-xz
d_x'91'y'45'z'93''8776'xy'45'xz_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'91'y'45'z'93''8776'xy'45'xz_290 ~v0 ~v1 v2 v3 v4 v5
  = du_x'91'y'45'z'93''8776'xy'45'xz_290 v2 v3 v4 v5
du_x'91'y'45'z'93''8776'xy'45'xz_290 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'91'y'45'z'93''8776'xy'45'xz_290 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
         (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
          coe
            (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                  (coe v5) (coe v2) (coe v3)))))
      (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
       coe
         (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
               (coe v5) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v3))))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                       (coe v8)))))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
            (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                     (coe v5) (coe v2) (coe v3)))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3)))
         (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
          coe
            (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                  (coe v5) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v3))))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe v7) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                          (coe v8)))))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                  (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3)))
            (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                     (coe v5) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v3))))
            (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                     (coe v5) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v3))))
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v4
                                 = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                           coe
                             (let v5
                                    = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                        (coe v4) in
                              coe
                                (let v6
                                       = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                                 coe
                                   (let v7
                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                              (coe v6) in
                                    coe
                                      (let v8
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                 (coe v7) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                               (coe v8))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v4))
                  (let v5 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
                   coe
                     (let v6 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v5)
                           (coe v6) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v3))))))
            (let v4
                   = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (let v10
                                     = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                            (coe v9) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                       v11
                                       (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (coe v10)))
                                       (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v2)
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                          (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3))
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                          (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1 v3))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                          (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                            (coe
                                                               MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                               (coe v0))))))))
                                          (coe
                                             MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                                v3))
                                          (coe
                                             MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v1
                                             (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3))
                                          (coe
                                             du_'45''8255'distrib'691''45''42'_270 (coe v0) (coe v1)
                                             (coe v3)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Structures.du_distrib'737'_2396
            (MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0)) v1
            v2 (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3)))
-- Algebra.Properties.RingWithoutOne.[y-z]x≈yx-zx
d_'91'y'45'z'93'x'8776'yx'45'zx_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'91'y'45'z'93'x'8776'yx'45'zx_304 ~v0 ~v1 v2 v3 v4 v5
  = du_'91'y'45'z'93'x'8776'yx'45'zx_304 v2 v3 v4 v5
du_'91'y'45'z'93'x'8776'yx'45'zx_304 ::
  MAlonzo.Code.Algebra.Bundles.T_RingWithoutOne_3370 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'91'y'45'z'93'x'8776'yx'45'zx_304 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
         (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
          coe
            (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                  (coe v5) (coe v2) (coe v3))))
         v1)
      (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
       coe
         (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
               (coe v5) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v2 v1)
               (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v3 v1))))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                            coe
                              (let v8
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                       (coe v8)))))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
            (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                     (coe v5) (coe v2) (coe v3))))
            v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v2 v1)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
               (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3) v1))
         (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
          coe
            (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                  (coe v5) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v3 v1))))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                   (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                            coe
                              (let v7
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                               coe
                                 (let v8
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe v7) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                          (coe v8)))))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'43'__3394 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v2 v1)
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3) v1))
            (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                     (coe v5) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v3 v1))))
            (let v4 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v4)
                     (coe v5) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v3 v1))))
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v4
                                 = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
                           coe
                             (let v5
                                    = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                        (coe v4) in
                              coe
                                (let v6
                                       = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                                 coe
                                   (let v7
                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                              (coe v6) in
                                    coe
                                      (let v8
                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                 (coe v7) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                               (coe v8))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v4))
                  (let v5 = MAlonzo.Code.Algebra.Bundles.d__'43'__3394 (coe v0) in
                   coe
                     (let v6 = MAlonzo.Code.Algebra.Bundles.d_'45'__3398 (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v5)
                           (coe v6) (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v2 v1)
                           (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v3 v1))))))
            (let v4
                   = MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (let v10
                                     = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                            (coe v9) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                       v11
                                       (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (coe v10)))
                                       (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v2 v1)
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                          (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3) v1)
                                       (coe
                                          MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                          (coe MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v3 v1))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                          (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                                                            (coe
                                                               MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402
                                                               (coe v0))))))))
                                          (coe
                                             MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0 v3
                                                v1))
                                          (coe
                                             MAlonzo.Code.Algebra.Bundles.d__'42'__3396 v0
                                             (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3)
                                             v1)
                                          (coe
                                             du_'45''8255'distrib'737''45''42'_260 (coe v0) (coe v3)
                                             (coe v1)))))))))))))
         (coe
            MAlonzo.Code.Algebra.Structures.du_distrib'691'_2398
            (MAlonzo.Code.Algebra.Bundles.d_isRingWithoutOne_3402 (coe v0)) v1
            v2 (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3398 v0 v3)))
