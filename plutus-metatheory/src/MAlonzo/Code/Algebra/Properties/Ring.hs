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

module MAlonzo.Code.Algebra.Properties.Ring where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Properties.AbelianGroup
import qualified MAlonzo.Code.Algebra.Properties.Group
import qualified MAlonzo.Code.Algebra.Properties.Loop
import qualified MAlonzo.Code.Algebra.Properties.QQuasigroup
import qualified MAlonzo.Code.Algebra.Properties.RingWithoutOne
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Properties.Ring._.cancel
d_cancel_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_366 ~v0 ~v1 v2 = du_cancel_366 v2
du_cancel_366 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_366 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel_308
               (coe
                  MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564
                  (coe v3)))))
-- Algebra.Properties.Ring._.cancelʳ
d_cancel'691'_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_368 ~v0 ~v1 v2 = du_cancel'691'_368 v2
du_cancel'691'_368 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_368 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'691'_298
               (coe
                  MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564
                  (coe v3)))))
-- Algebra.Properties.Ring._.cancelˡ
d_cancel'737'_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_370 ~v0 ~v1 v2 = du_cancel'737'_370 v2
du_cancel'737'_370 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_370 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'737'_288
               (coe
                  MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564
                  (coe v3)))))
-- Algebra.Properties.Ring._.identity-unique
d_identity'45'unique_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_identity'45'unique_372 ~v0 ~v1 v2 = du_identity'45'unique_372 v2
du_identity'45'unique_372 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_identity'45'unique_372 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Properties.Loop.du_identity'45'unique_326
               (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_580 (coe v3)))))
-- Algebra.Properties.Ring._.identityʳ-unique
d_identity'691''45'unique_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'691''45'unique_374 ~v0 ~v1 v2
  = du_identity'691''45'unique_374 v2
du_identity'691''45'unique_374 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_identity'691''45'unique_374 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Properties.Loop.du_identity'691''45'unique_316
               (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_580 (coe v3)))))
-- Algebra.Properties.Ring._.identityˡ-unique
d_identity'737''45'unique_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'737''45'unique_376 ~v0 ~v1 v2
  = du_identity'737''45'unique_376 v2
du_identity'737''45'unique_376 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_identity'737''45'unique_376 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Properties.Loop.du_identity'737''45'unique_304
               (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_580 (coe v3)))))
-- Algebra.Properties.Ring._.inverseʳ-unique
d_inverse'691''45'unique_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691''45'unique_378 ~v0 ~v1 v2
  = du_inverse'691''45'unique_378 v2
du_inverse'691''45'unique_378 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691''45'unique_378 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_inverse'691''45'unique_606
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.inverseˡ-unique
d_inverse'737''45'unique_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737''45'unique_380 ~v0 ~v1 v2
  = du_inverse'737''45'unique_380 v2
du_inverse'737''45'unique_380 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'737''45'unique_380 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_inverse'737''45'unique_594
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.ε⁻¹≈ε
d_ε'8315''185''8776'ε_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 -> AgdaAny
d_ε'8315''185''8776'ε_382 ~v0 ~v1 v2
  = du_ε'8315''185''8776'ε_382 v2
du_ε'8315''185''8776'ε_382 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 -> AgdaAny
du_ε'8315''185''8776'ε_382 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_ε'8315''185''8776'ε_614
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.⁻¹-∙-comm
d_'8315''185''45''8729''45'comm_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45''8729''45'comm_384 ~v0 ~v1 v2
  = du_'8315''185''45''8729''45'comm_384 v2
du_'8315''185''45''8729''45'comm_384 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45''8729''45'comm_384 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.AbelianGroup.du_'8315''185''45''8729''45'comm_244
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
            (coe v1)))
-- Algebra.Properties.Ring._.⁻¹-anti-homo-∙
d_'8315''185''45'anti'45'homo'45''8729'_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''8729'_386 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''8729'_386 v2
du_'8315''185''45'anti'45'homo'45''8729'_386 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''8729'_386 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''8729'_656
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.-‿distribʳ-*
d_'45''8255'distrib'691''45''42'_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'distrib'691''45''42'_388 ~v0 ~v1 v2
  = du_'45''8255'distrib'691''45''42'_388 v2
du_'45''8255'distrib'691''45''42'_388 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255'distrib'691''45''42'_388 v0
  = coe
      MAlonzo.Code.Algebra.Properties.RingWithoutOne.du_'45''8255'distrib'691''45''42'_270
      (coe MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0))
-- Algebra.Properties.Ring._.-‿distribˡ-*
d_'45''8255'distrib'737''45''42'_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'45''8255'distrib'737''45''42'_390 ~v0 ~v1 v2
  = du_'45''8255'distrib'737''45''42'_390 v2
du_'45''8255'distrib'737''45''42'_390 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'45''8255'distrib'737''45''42'_390 v0
  = coe
      MAlonzo.Code.Algebra.Properties.RingWithoutOne.du_'45''8255'distrib'737''45''42'_260
      (coe MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0))
-- Algebra.Properties.Ring._.⁻¹-injective
d_'8315''185''45'injective_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'injective_392 ~v0 ~v1 v2
  = du_'8315''185''45'injective_392 v2
du_'8315''185''45'injective_392 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'injective_392 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'injective_650
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.⁻¹-involutive
d_'8315''185''45'involutive_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 -> AgdaAny -> AgdaAny
d_'8315''185''45'involutive_394 ~v0 ~v1 v2
  = du_'8315''185''45'involutive_394 v2
du_'8315''185''45'involutive_394 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 -> AgdaAny -> AgdaAny
du_'8315''185''45'involutive_394 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'involutive_624
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.//-cong₂
d_'47''47''45'cong'8322'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'8322'_396 ~v0 ~v1 v2
  = du_'47''47''45'cong'8322'_396 v2
du_'47''47''45'cong'8322'_396 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'8322'_396 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'cong'8322'_528
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.//-rightDivides
d_'47''47''45'rightDivides_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'47''47''45'rightDivides_398 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides_398 v2
du_'47''47''45'rightDivides_398 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'47''47''45'rightDivides_398 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides_560
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.//-rightDividesʳ
d_'47''47''45'rightDivides'691'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'rightDivides'691'_400 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides'691'_400 v2
du_'47''47''45'rightDivides'691'_400 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'rightDivides'691'_400 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides'691'_554
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.//-rightDividesˡ
d_'47''47''45'rightDivides'737'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'rightDivides'737'_402 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides'737'_402 v2
du_'47''47''45'rightDivides'737'_402 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'rightDivides'737'_402 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides'737'_548
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.[y-z]x≈yx-zx
d_'91'y'45'z'93'x'8776'yx'45'zx_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'91'y'45'z'93'x'8776'yx'45'zx_404 ~v0 ~v1 v2
  = du_'91'y'45'z'93'x'8776'yx'45'zx_404 v2
du_'91'y'45'z'93'x'8776'yx'45'zx_404 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'91'y'45'z'93'x'8776'yx'45'zx_404 v0
  = coe
      MAlonzo.Code.Algebra.Properties.RingWithoutOne.du_'91'y'45'z'93'x'8776'yx'45'zx_304
      (coe MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0))
-- Algebra.Properties.Ring._.\\-cong₂
d_'92''92''45'cong'8322'_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'8322'_406 ~v0 ~v1 v2
  = du_'92''92''45'cong'8322'_406 v2
du_'92''92''45'cong'8322'_406 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'8322'_406 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'cong'8322'_522
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.\\-leftDivides
d_'92''92''45'leftDivides_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'92''92''45'leftDivides_408 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides_408 v2
du_'92''92''45'leftDivides_408 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'92''92''45'leftDivides_408 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides_546
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.\\-leftDividesʳ
d_'92''92''45'leftDivides'691'_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'leftDivides'691'_410 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides'691'_410 v2
du_'92''92''45'leftDivides'691'_410 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'leftDivides'691'_410 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides'691'_540
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.\\-leftDividesˡ
d_'92''92''45'leftDivides'737'_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'leftDivides'737'_412 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides'737'_412 v2
du_'92''92''45'leftDivides'737'_412 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'leftDivides'737'_412 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides'737'_534
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.\\≗flip-//⇒comm
d_'92''92''8791'flip'45''47''47''8658'comm_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''8791'flip'45''47''47''8658'comm_414 ~v0 ~v1 v2
  = du_'92''92''8791'flip'45''47''47''8658'comm_414 v2
du_'92''92''8791'flip'45''47''47''8658'comm_414 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''8791'flip'45''47''47''8658'comm_414 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'92''92''8791'flip'45''47''47''8658'comm_686
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.comm⇒\\≗flip-//
d_comm'8658''92''92''8791'flip'45''47''47'_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm'8658''92''92''8791'flip'45''47''47'_416 ~v0 ~v1 v2
  = du_comm'8658''92''92''8791'flip'45''47''47'_416 v2
du_comm'8658''92''92''8791'flip'45''47''47'_416 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm'8658''92''92''8791'flip'45''47''47'_416 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_comm'8658''92''92''8791'flip'45''47''47'_698
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.isLoop
d_isLoop_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3046
d_isLoop_418 ~v0 ~v1 v2 = du_isLoop_418 v2
du_isLoop_418 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3046
du_isLoop_418 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_isLoop_578
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.isQuasigroup
d_isQuasigroup_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2964
d_isQuasigroup_420 ~v0 ~v1 v2 = du_isQuasigroup_420 v2
du_isQuasigroup_420 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2964
du_isQuasigroup_420 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_isQuasigroup_562
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.loop
d_loop_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Algebra.Bundles.T_Loop_4384
d_loop_422 ~v0 ~v1 v2 = du_loop_422 v2
du_loop_422 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Algebra.Bundles.T_Loop_4384
du_loop_422 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_loop_580
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.quasigroup
d_quasigroup_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4284
d_quasigroup_424 ~v0 ~v1 v2 = du_quasigroup_424 v2
du_quasigroup_424 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4284
du_quasigroup_424 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.x+x≈x⇒x≈0
d_x'43'x'8776'x'8658'x'8776'0_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'43'x'8776'x'8658'x'8776'0_426 ~v0 ~v1 v2
  = du_x'43'x'8776'x'8658'x'8776'0_426 v2
du_x'43'x'8776'x'8658'x'8776'0_426 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'43'x'8776'x'8658'x'8776'0_426 v0
  = coe
      MAlonzo.Code.Algebra.Properties.RingWithoutOne.du_x'43'x'8776'x'8658'x'8776'0_278
      (coe MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0))
-- Algebra.Properties.Ring._.x[y-z]≈xy-xz
d_x'91'y'45'z'93''8776'xy'45'xz_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'91'y'45'z'93''8776'xy'45'xz_428 ~v0 ~v1 v2
  = du_x'91'y'45'z'93''8776'xy'45'xz_428 v2
du_x'91'y'45'z'93''8776'xy'45'xz_428 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'91'y'45'z'93''8776'xy'45'xz_428 v0
  = coe
      MAlonzo.Code.Algebra.Properties.RingWithoutOne.du_x'91'y'45'z'93''8776'xy'45'xz_290
      (coe MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0))
-- Algebra.Properties.Ring._.xyx⁻¹≈y
d_xyx'8315''185''8776'y_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_xyx'8315''185''8776'y_430 ~v0 ~v1 v2
  = du_xyx'8315''185''8776'y_430 v2
du_xyx'8315''185''8776'y_430 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_xyx'8315''185''8776'y_430 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.AbelianGroup.du_xyx'8315''185''8776'y_234
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
            (coe v1)))
-- Algebra.Properties.Ring._.x∙y⁻¹≈ε⇒x≈y
d_x'8729'y'8315''185''8776'ε'8658'x'8776'y_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'y'8315''185''8776'ε'8658'x'8776'y_432 ~v0 ~v1 v2
  = du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_432 v2
du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_432 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_432 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_630
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.x≈y⇒x∙y⁻¹≈ε
d_x'8776'y'8658'x'8729'y'8315''185''8776'ε_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'y'8658'x'8729'y'8315''185''8776'ε_434 ~v0 ~v1 v2
  = du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_434 v2
du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_434 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_434 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_642
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.x≈z//y
d_x'8776'z'47''47'y_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'z'47''47'y_436 ~v0 ~v1 v2 = du_x'8776'z'47''47'y_436 v2
du_x'8776'z'47''47'y_436 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'z'47''47'y_436 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Properties.QQuasigroup.du_x'8776'z'47''47'y_278
               (coe
                  MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564
                  (coe v3)))))
-- Algebra.Properties.Ring._.y≈x\\z
d_y'8776'x'92''92'z_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8776'x'92''92'z_438 ~v0 ~v1 v2 = du_y'8776'x'92''92'z_438 v2
du_y'8776'x'92''92'z_438 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8776'x'92''92'z_438 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Properties.QQuasigroup.du_y'8776'x'92''92'z_262
               (coe
                  MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_564
                  (coe v3)))))
-- Algebra.Properties.Ring._.⁻¹-anti-homo-//
d_'8315''185''45'anti'45'homo'45''47''47'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''47''47'_440 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''47''47'_440 v2
du_'8315''185''45'anti'45'homo'45''47''47'_440 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''47''47'_440 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''47''47'_666
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.⁻¹-anti-homo-\\
d_'8315''185''45'anti'45'homo'45''92''92'_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''92''92'_442 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''92''92'_442 v2
du_'8315''185''45'anti'45'homo'45''92''92'_442 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''92''92'_442 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''92''92'_676
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring._.⁻¹-anti-homo‿-
d_'8315''185''45'anti'45'homo'8255''45'_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'8255''45'_444 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'8255''45'_444 v2
du_'8315''185''45'anti'45'homo'8255''45'_444 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'8255''45'_444 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.AbelianGroup.du_'8315''185''45'anti'45'homo'8255''45'_228
         (coe
            MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
            (coe v1)))
-- Algebra.Properties.Ring._.⁻¹-selfInverse
d_'8315''185''45'selfInverse_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'selfInverse_446 ~v0 ~v1 v2
  = du_'8315''185''45'selfInverse_446 v2
du_'8315''185''45'selfInverse_446 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'selfInverse_446 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Bundles.du_'43''45'abelianGroup_3506
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'selfInverse_616
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1736 (coe v2))))
-- Algebra.Properties.Ring.-1*x≈-x
d_'45'1'42'x'8776''45'x_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 -> AgdaAny -> AgdaAny
d_'45'1'42'x'8776''45'x_450 ~v0 ~v1 v2 v3
  = du_'45'1'42'x'8776''45'x_450 v2 v3
du_'45'1'42'x'8776''45'x_450 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838 -> AgdaAny -> AgdaAny
du_'45'1'42'x'8776''45'x_450 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'42'__3866 v0
         (coe
            MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0
            (MAlonzo.Code.Algebra.Bundles.d_1'35'_3872 (coe v0)))
         v1)
      (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0 v1)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2 = MAlonzo.Code.Algebra.Bundles.d_isRing_3874 (coe v0) in
                   coe
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                (coe v2) in
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
                                          (coe v7))))))))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v2 = MAlonzo.Code.Algebra.Bundles.d_isRing_3874 (coe v0) in
                coe
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                             (coe v2) in
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
                                       (coe v7)))))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'42'__3866 v0
            (coe
               MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0
               (MAlonzo.Code.Algebra.Bundles.d_1'35'_3872 (coe v0)))
            v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'42'__3866 v0
               (MAlonzo.Code.Algebra.Bundles.d_1'35'_3872 (coe v0)) v1))
         (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0 v1)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v2 = MAlonzo.Code.Algebra.Bundles.d_isRing_3874 (coe v0) in
                      coe
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                   (coe v2) in
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
                                             (coe v7))))))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'42'__3866 v0
                  (MAlonzo.Code.Algebra.Bundles.d_1'35'_3872 (coe v0)) v1))
            (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0 v1)
            (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0 v1)
            (let v2
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v2 = MAlonzo.Code.Algebra.Bundles.d_isRing_3874 (coe v0) in
                           coe
                             (let v3
                                    = coe
                                        MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                        (coe v2) in
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
                                                  (coe v7)))))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v2))
                  (coe MAlonzo.Code.Algebra.Bundles.d_'45'__3868 v0 v1)))
            (let v2 = MAlonzo.Code.Algebra.Bundles.d_isRing_3874 (coe v0) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052
                  (MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v2)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'42'__3866 v0
                     (MAlonzo.Code.Algebra.Bundles.d_1'35'_3872 (coe v0)) v1)
                  v1
                  (let v3 = MAlonzo.Code.Algebra.Bundles.d__'43'__3864 (coe v0) in
                   coe
                     (let v4 = MAlonzo.Code.Algebra.Bundles.d__'42'__3866 (coe v0) in
                      coe
                        (let v5 = MAlonzo.Code.Algebra.Bundles.d_'45'__3868 (coe v0) in
                         coe
                           (let v6 = MAlonzo.Code.Algebra.Bundles.d_0'35'_3870 (coe v0) in
                            coe
                              (let v7 = MAlonzo.Code.Algebra.Bundles.d_isRing_3874 (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790
                                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
                                    v1)))))))))
         (coe
            MAlonzo.Code.Algebra.Properties.RingWithoutOne.du_'45''8255'distrib'737''45''42'_260
            (coe MAlonzo.Code.Algebra.Bundles.du_ringWithoutOne_3988 (coe v0))
            (coe MAlonzo.Code.Algebra.Bundles.d_1'35'_3872 (coe v0)) (coe v1)))
