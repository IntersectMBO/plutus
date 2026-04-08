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

module MAlonzo.Code.Algebra.Structures.Biased where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Consequences.Setoid
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Structures.Biased._._DistributesOver_
d__DistributesOver__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__18 = erased
-- Algebra.Structures.Biased._._DistributesOverʳ_
d__DistributesOver'691'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__20 = erased
-- Algebra.Structures.Biased._._DistributesOverˡ_
d__DistributesOver'737'__22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__22 = erased
-- Algebra.Structures.Biased._.Commutative
d_Commutative_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_42 = erased
-- Algebra.Structures.Biased._.LeftIdentity
d_LeftIdentity_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftIdentity_84 = erased
-- Algebra.Structures.Biased._.LeftZero
d_LeftZero_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftZero_92 = erased
-- Algebra.Structures.Biased._.RightIdentity
d_RightIdentity_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightIdentity_114 = erased
-- Algebra.Structures.Biased._.RightZero
d_RightZero_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightZero_122 = erased
-- Algebra.Structures.Biased._.Zero
d_Zero_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Zero_142 = erased
-- Algebra.Structures.Biased._.IsAbelianGroup
d_IsAbelianGroup_146 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Structures.Biased._.IsCommutativeMonoid
d_IsCommutativeMonoid_170 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Structures.Biased._.IsCommutativeSemiring
d_IsCommutativeSemiring_182 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Structures.Biased._.IsMonoid
d_IsMonoid_246 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Structures.Biased._.IsNearSemiring
d_IsNearSemiring_254 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Structures.Biased._.IsRing
d_IsRing_278 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Algebra.Structures.Biased._.IsSemigroup
d_IsSemigroup_290 a0 a1 a2 a3 a4 = ()
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_302 a0 a1 a2 a3 a4 a5 a6 a7
  = ()
-- Algebra.Structures.Biased._.IsSemiringWithoutOne
d_IsSemiringWithoutOne_306 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Structures.Biased._.IsAbelianGroup._//_
d__'47''47'__320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__320 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7
  = du__'47''47'__320 v4 v6
du__'47''47'__320 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__320 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Algebra.Structures.Biased._.IsAbelianGroup.comm
d_comm_324 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_324 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_1186 (coe v0)
-- Algebra.Structures.Biased._.IsAbelianGroup.identityʳ
d_identity'691'_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny
d_identity'691'_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_328 v7
du_identity'691'_328 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny
du_identity'691'_328 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_754
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1)))
-- Algebra.Structures.Biased._.IsAbelianGroup.identityˡ
d_identity'737'_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny
d_identity'737'_330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_330 v7
du_identity'737'_330 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny
du_identity'737'_330 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'737'_752
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1)))
-- Algebra.Structures.Biased._.IsAbelianGroup.inverseʳ
d_inverse'691'_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny
d_inverse'691'_334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_334 v7
du_inverse'691'_334 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny
du_inverse'691'_334 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_inverse'691'_1146
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.inverseˡ
d_inverse'737'_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny
d_inverse'737'_336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_336 v7
du_inverse'737'_336 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny
du_inverse'737'_336 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_inverse'737'_1144
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.isCommutativeMagma
d_isCommutativeMagma_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_338 v7
du_isCommutativeMagma_338 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_338 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Algebra.Structures.Biased._.IsAbelianGroup.isCommutativeMonoid
d_isCommutativeMonoid_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_340 ~v0 ~v1 ~v2 ~v3
  = du_isCommutativeMonoid_340
du_isCommutativeMonoid_340 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_340 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244 v3
-- Algebra.Structures.Biased._.IsAbelianGroup.isCommutativeSemigroup
d_isCommutativeSemigroup_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeSemigroup_342 v7
du_isCommutativeSemigroup_342 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_342 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
         (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.isGroup
d_isGroup_346 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_346 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)
-- Algebra.Structures.Biased._.IsAbelianGroup.isInvertibleMagma
d_isInvertibleMagma_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleMagma_348 v7
du_isInvertibleMagma_348 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_348 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleUnitalMagma_350 v7
du_isInvertibleUnitalMagma_350 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_350 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.isPartialEquivalence
d_isPartialEquivalence_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_356 v7
du_isPartialEquivalence_356 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_356 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))))))
-- Algebra.Structures.Biased._.IsAbelianGroup.isUnitalMagma
d_isUnitalMagma_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_360 v7
du_isUnitalMagma_360 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_360 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1)))
-- Algebra.Structures.Biased._.IsAbelianGroup.reflexive
d_reflexive_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_364 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_364 v7
du_reflexive_364 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_364 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))
                    v5))))
-- Algebra.Structures.Biased._.IsAbelianGroup.setoid
d_setoid_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_366 v7
du_setoid_366 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_366 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Algebra.Structures.Biased._.IsAbelianGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_372 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'691''45''8315''185'_372 v4 v5 v6 v7
du_unique'691''45''8315''185'_372 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_372 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1158
      (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v3))
-- Algebra.Structures.Biased._.IsAbelianGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_374 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'737''45''8315''185'_374 v4 v5 v6 v7
du_unique'737''45''8315''185'_374 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_374 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1152
      (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v3))
-- Algebra.Structures.Biased._.IsAbelianGroup.∙-congʳ
d_'8729''45'cong'691'_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_380 v7
du_'8729''45'cong'691'_380 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_380 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.Biased._.IsAbelianGroup.∙-congˡ
d_'8729''45'cong'737'_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_382 v7
du_'8729''45'cong'737'_382 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_382 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Structures.Biased._.IsCommutativeMonoid.comm
d_comm_614 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_614 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_776 (coe v0)
-- Algebra.Structures.Biased._.IsCommutativeMonoid.isMonoid
d_isMonoid_630 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_630 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)
-- Algebra.Structures.Biased._.IsCommutativeSemiring.*-comm
d_'42''45'comm_814 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_814 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1766 (coe v0)
-- Algebra.Structures.Biased._.IsCommutativeSemiring.isSemiring
d_isSemiring_884 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_884 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)
-- Algebra.Structures.Biased._.IsMonoid.identity
d_identity_1696 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1696 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_724 (coe v0)
-- Algebra.Structures.Biased._.IsMonoid.identityʳ
d_identity'691'_1698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny -> AgdaAny
d_identity'691'_1698 ~v0 ~v1 ~v2 ~v3 = du_identity'691'_1698
du_identity'691'_1698 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny -> AgdaAny
du_identity'691'_1698 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_identity'691'_754 v2
-- Algebra.Structures.Biased._.IsMonoid.identityˡ
d_identity'737'_1700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny -> AgdaAny
d_identity'737'_1700 ~v0 ~v1 ~v2 ~v3 = du_identity'737'_1700
du_identity'737'_1700 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny -> AgdaAny
du_identity'737'_1700 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_identity'737'_752 v2
-- Algebra.Structures.Biased._.IsMonoid.isPartialEquivalence
d_isPartialEquivalence_1706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_1706 v6
du_isPartialEquivalence_1706 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1706 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Algebra.Structures.Biased._.IsMonoid.isSemigroup
d_isSemigroup_1708 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1708 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)
-- Algebra.Structures.Biased._.IsMonoid.isUnitalMagma
d_isUnitalMagma_1710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1710 ~v0 ~v1 ~v2 ~v3 = du_isUnitalMagma_1710
du_isUnitalMagma_1710 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1710 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756 v2
-- Algebra.Structures.Biased._.IsMonoid.reflexive
d_reflexive_1714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_1714 v6
du_reflexive_1714 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1714 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))
              v3))
-- Algebra.Structures.Biased._.IsMonoid.setoid
d_setoid_1716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_1716 v6
du_setoid_1716 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1716 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Algebra.Structures.Biased._.IsMonoid.∙-congʳ
d_'8729''45'cong'691'_1724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_1724 v6
du_'8729''45'cong'691'_1724 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1724 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.Biased._.IsMonoid.∙-congˡ
d_'8729''45'cong'737'_1726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_1726 v6
du_'8729''45'cong'737'_1726 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1726 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                  (coe v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                        (coe v3)))))))
-- Algebra.Structures.Biased._.IsNearSemiring.*-assoc
d_'42''45'assoc_1796 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1796 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1282 (coe v0)
-- Algebra.Structures.Biased._.IsNearSemiring.*-cong
d_'42''45'cong_1798 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1798 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1280 (coe v0)
-- Algebra.Structures.Biased._.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1824 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1824 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0)
-- Algebra.Structures.Biased._.IsNearSemiring.distribʳ
d_distrib'691'_1830 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1830 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib'691'_1284 (coe v0)
-- Algebra.Structures.Biased._.IsNearSemiring.zeroˡ
d_zero'737'_1846 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  AgdaAny -> AgdaAny
d_zero'737'_1846 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero'737'_1286 (coe v0)
-- Algebra.Structures.Biased._.IsRing.*-assoc
d_'42''45'assoc_2214 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2214 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2766 (coe v0)
-- Algebra.Structures.Biased._.IsRing.*-cong
d_'42''45'cong_2216 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2216 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_2764 (coe v0)
-- Algebra.Structures.Biased._.IsRing.*-identity
d_'42''45'identity_2222 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2222 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768 (coe v0)
-- Algebra.Structures.Biased._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2250 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2250 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe v0)
-- Algebra.Structures.Biased._.IsRing.distrib
d_distrib_2280 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2280 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2770 (coe v0)
-- Algebra.Structures.Biased._.IsSemigroup.assoc
d_assoc_2442 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2442 v0
  = coe MAlonzo.Code.Algebra.Structures.d_assoc_498 (coe v0)
-- Algebra.Structures.Biased._.IsSemigroup.isMagma
d_isMagma_2446 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2446 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2582 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2582 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1560 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2584 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2584 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1558 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2590 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2590 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2620 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2620 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2632 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2632 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1564 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2654 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2654 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1364 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2656 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2656 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1362 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2684 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2684 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.distrib
d_distrib_2690 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2690 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1366 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.zero
d_zero_2712 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2712 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1368 (coe v0)
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ
d_IsCommutativeMonoid'737'_2770 a0 a1 a2 a3 a4 a5 = ()
data T_IsCommutativeMonoid'737'_2770
  = C_constructor_2820 MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
                       (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ.isSemigroup
d_isSemigroup_2782 ::
  T_IsCommutativeMonoid'737'_2770 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2782 v0
  = case coe v0 of
      C_constructor_2820 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ.identityˡ
d_identity'737'_2784 ::
  T_IsCommutativeMonoid'737'_2770 -> AgdaAny -> AgdaAny
d_identity'737'_2784 v0
  = case coe v0 of
      C_constructor_2820 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ.comm
d_comm_2786 ::
  T_IsCommutativeMonoid'737'_2770 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2786 v0
  = case coe v0 of
      C_constructor_2820 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ.isCommutativeMonoid
d_isCommutativeMonoid_2788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid'737'_2770 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2788 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCommutativeMonoid_2788 v4 v5 v6
du_isCommutativeMonoid_2788 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid'737'_2770 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2788 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_758
         (coe d_isSemigroup_2782 (coe v2))
         (coe
            MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'id'737''8658'id_372
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe d_isSemigroup_2782 (coe v2))))
            (coe v0) (coe d_comm_2786 (coe v2)) (coe v1)
            (coe d_identity'737'_2784 (coe v2))))
      (coe d_comm_2786 (coe v2))
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ
d_IsCommutativeMonoid'691'_2826 a0 a1 a2 a3 a4 a5 = ()
data T_IsCommutativeMonoid'691'_2826
  = C_constructor_2876 MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
                       (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ.isSemigroup
d_isSemigroup_2838 ::
  T_IsCommutativeMonoid'691'_2826 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2838 v0
  = case coe v0 of
      C_constructor_2876 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ.identityʳ
d_identity'691'_2840 ::
  T_IsCommutativeMonoid'691'_2826 -> AgdaAny -> AgdaAny
d_identity'691'_2840 v0
  = case coe v0 of
      C_constructor_2876 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ.comm
d_comm_2842 ::
  T_IsCommutativeMonoid'691'_2826 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2842 v0
  = case coe v0 of
      C_constructor_2876 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ.isCommutativeMonoid
d_isCommutativeMonoid_2844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid'691'_2826 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2844 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCommutativeMonoid_2844 v4 v5 v6
du_isCommutativeMonoid_2844 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid'691'_2826 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2844 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_758
         (coe d_isSemigroup_2838 (coe v2))
         (coe
            MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'id'691''8658'id_376
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe d_isSemigroup_2838 (coe v2))))
            (coe v0) (coe d_comm_2842 (coe v2)) (coe v1)
            (coe d_identity'691'_2840 (coe v2))))
      (coe d_comm_2842 (coe v2))
-- Algebra.Structures.Biased.IsSemiringWithoutOne*
d_IsSemiringWithoutOne'42'_2884 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringWithoutOne'42'_2884
  = C_constructor_2940 MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
                       MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2900 ::
  T_IsSemiringWithoutOne'42'_2884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2900 v0
  = case coe v0 of
      C_constructor_2940 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.*-isSemigroup
d_'42''45'isSemigroup_2902 ::
  T_IsSemiringWithoutOne'42'_2884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2902 v0
  = case coe v0 of
      C_constructor_2940 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.distrib
d_distrib_2904 ::
  T_IsSemiringWithoutOne'42'_2884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2904 v0
  = case coe v0 of
      C_constructor_2940 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.zero
d_zero_2906 ::
  T_IsSemiringWithoutOne'42'_2884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2906 v0
  = case coe v0 of
      C_constructor_2940 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.isSemiringWithoutOne
d_isSemiringWithoutOne_2908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne'42'_2884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2908 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isSemiringWithoutOne_2908 v7
du_isSemiringWithoutOne_2908 ::
  T_IsSemiringWithoutOne'42'_2884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2908 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1430
      (coe d_'43''45'isCommutativeMonoid_2900 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe d_'42''45'isSemigroup_2902 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe d_'42''45'isSemigroup_2902 (coe v0)))
      (coe d_distrib_2904 (coe v0)) (coe d_zero_2906 (coe v0))
-- Algebra.Structures.Biased.IsNearSemiring*
d_IsNearSemiring'42'_2948 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiring'42'_2948
  = C_constructor_3004 MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
                       MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsNearSemiring*.+-isMonoid
d_'43''45'isMonoid_2964 ::
  T_IsNearSemiring'42'_2948 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_2964 v0
  = case coe v0 of
      C_constructor_3004 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsNearSemiring*.*-isSemigroup
d_'42''45'isSemigroup_2966 ::
  T_IsNearSemiring'42'_2948 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2966 v0
  = case coe v0 of
      C_constructor_3004 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsNearSemiring*.distribʳ
d_distrib'691'_2968 ::
  T_IsNearSemiring'42'_2948 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2968 v0
  = case coe v0 of
      C_constructor_3004 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsNearSemiring*.zeroˡ
d_zero'737'_2970 :: T_IsNearSemiring'42'_2948 -> AgdaAny -> AgdaAny
d_zero'737'_2970 v0
  = case coe v0 of
      C_constructor_3004 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsNearSemiring*.isNearSemiring
d_isNearSemiring_2972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring'42'_2948 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2972 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiring_2972 v7
du_isNearSemiring_2972 ::
  T_IsNearSemiring'42'_2948 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_2972 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1334
      (coe d_'43''45'isMonoid_2964 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe d_'42''45'isSemigroup_2966 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe d_'42''45'isSemigroup_2966 (coe v0)))
      (coe d_distrib'691'_2968 (coe v0)) (coe d_zero'737'_2970 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*
d_IsSemiringWithoutAnnihilatingZero'42'_3014 a0 a1 a2 a3 a4 a5 a6
                                             a7
  = ()
data T_IsSemiringWithoutAnnihilatingZero'42'_3014
  = C_constructor_3078 MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
                       MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_3030 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_3030 v0
  = case coe v0 of
      C_constructor_3078 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*.*-isMonoid
d_'42''45'isMonoid_3032 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_3032 v0
  = case coe v0 of
      C_constructor_3078 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*.distrib
d_distrib_3034 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_3034 v0
  = case coe v0 of
      C_constructor_3078 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_3036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_3036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 v8
  = du_isSemiringWithoutAnnihilatingZero_3036 v8
du_isSemiringWithoutAnnihilatingZero_3036 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
du_isSemiringWithoutAnnihilatingZero_3036 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1630
      (coe d_'43''45'isCommutativeMonoid_3030 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe d_'42''45'isMonoid_3032 (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe d_'42''45'isMonoid_3032 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_724
         (coe d_'42''45'isMonoid_3032 (coe v0)))
      (coe d_distrib_3034 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.identityʳ
d_identity'691'_3048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 -> AgdaAny -> AgdaAny
d_identity'691'_3048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_3048 v8
du_identity'691'_3048 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 -> AgdaAny -> AgdaAny
du_identity'691'_3048 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'691'_754
      (coe d_'42''45'isMonoid_3032 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.identityˡ
d_identity'737'_3050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 -> AgdaAny -> AgdaAny
d_identity'737'_3050 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_3050 v8
du_identity'737'_3050 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 -> AgdaAny -> AgdaAny
du_identity'737'_3050 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'737'_752
      (coe d_'42''45'isMonoid_3032 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.isPartialEquivalence
d_isPartialEquivalence_3056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3056 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_3056 v8
du_isPartialEquivalence_3056 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3056 v0
  = let v1 = d_'42''45'isMonoid_3032 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.isUnitalMagma
d_isUnitalMagma_3060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_3060 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_3060 v8
du_isUnitalMagma_3060 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_3060 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe d_'42''45'isMonoid_3032 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.reflexive
d_reflexive_3064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3064 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_3064 v8
du_reflexive_3064 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3064 v0
  = let v1 = d_'42''45'isMonoid_3032 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3))
                 v4)))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.setoid
d_setoid_3066 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3066 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_3066 v8
du_setoid_3066 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3066 v0
  = let v1 = d_'42''45'isMonoid_3032 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.∙-congʳ
d_'8729''45'cong'691'_3074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_3074 v8
du_'8729''45'cong'691'_3074 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3074 v0
  = let v1 = d_'42''45'isMonoid_3032 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.∙-congˡ
d_'8729''45'cong'737'_3076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3076 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_3076 v8
du_'8729''45'cong'737'_3076 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_3014 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3076 v0
  = let v1 = d_'42''45'isMonoid_3032 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ
d_IsCommutativeSemiring'737'_3088 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsCommutativeSemiring'737'_3088
  = C_constructor_3208 MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
                       MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_3106 ::
  T_IsCommutativeSemiring'737'_3088 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_3106 v0
  = case coe v0 of
      C_constructor_3208 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_3108 ::
  T_IsCommutativeSemiring'737'_3088 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_3108 v0
  = case coe v0 of
      C_constructor_3208 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.distribʳ
d_distrib'691'_3110 ::
  T_IsCommutativeSemiring'737'_3088 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_3110 v0
  = case coe v0 of
      C_constructor_3208 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.zeroˡ
d_zero'737'_3112 ::
  T_IsCommutativeSemiring'737'_3088 -> AgdaAny -> AgdaAny
d_zero'737'_3112 v0
  = case coe v0 of
      C_constructor_3208 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.isCommutativeSemiring
d_isCommutativeSemiring_3114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring'737'_3088 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_3114 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 v8
  = du_isCommutativeSemiring_3114 v4 v5 v6 v8
du_isCommutativeSemiring_3114 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiring'737'_3088 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
du_isCommutativeSemiring_3114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1740
         (coe
            MAlonzo.Code.Algebra.Structures.C_constructor_1630
            (coe d_'43''45'isCommutativeMonoid_3106 (coe v3))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                        (coe d_'42''45'isCommutativeMonoid_3108 (coe v3))))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_498
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                     (coe d_'42''45'isCommutativeMonoid_3108 (coe v3)))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_identity_724
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe d_'42''45'isCommutativeMonoid_3108 (coe v3))))
            (coe
               MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'691''8658'distr_560
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_202
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_496
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                           (coe d_'43''45'isCommutativeMonoid_3106 (coe v3))))))
               (coe v1) (coe v0)
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_496
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                           (coe d_'43''45'isCommutativeMonoid_3106 (coe v3))))))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_comm_776
                  (coe d_'42''45'isCommutativeMonoid_3108 (coe v3)))
               (coe d_distrib'691'_3110 (coe v3))))
         (coe
            MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'737''8658'ze_392
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                        (coe d_'43''45'isCommutativeMonoid_3106 (coe v3))))))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Structures.d_comm_776
               (coe d_'42''45'isCommutativeMonoid_3108 (coe v3)))
            (coe v2) (coe d_zero'737'_3112 (coe v3))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_776
         (coe d_'42''45'isCommutativeMonoid_3108 (coe v3)))
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ
d_IsCommutativeSemiring'691'_3218 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsCommutativeSemiring'691'_3218
  = C_constructor_3338 MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
                       MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_3236 ::
  T_IsCommutativeSemiring'691'_3218 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_3236 v0
  = case coe v0 of
      C_constructor_3338 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_3238 ::
  T_IsCommutativeSemiring'691'_3218 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_3238 v0
  = case coe v0 of
      C_constructor_3338 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.distribˡ
d_distrib'737'_3240 ::
  T_IsCommutativeSemiring'691'_3218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_3240 v0
  = case coe v0 of
      C_constructor_3338 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.zeroʳ
d_zero'691'_3242 ::
  T_IsCommutativeSemiring'691'_3218 -> AgdaAny -> AgdaAny
d_zero'691'_3242 v0
  = case coe v0 of
      C_constructor_3338 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.isCommutativeSemiring
d_isCommutativeSemiring_3244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring'691'_3218 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_3244 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 v8
  = du_isCommutativeSemiring_3244 v4 v5 v6 v8
du_isCommutativeSemiring_3244 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiring'691'_3218 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
du_isCommutativeSemiring_3244 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1740
         (coe
            MAlonzo.Code.Algebra.Structures.C_constructor_1630
            (coe d_'43''45'isCommutativeMonoid_3236 (coe v3))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                        (coe d_'42''45'isCommutativeMonoid_3238 (coe v3))))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_498
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                     (coe d_'42''45'isCommutativeMonoid_3238 (coe v3)))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_identity_724
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe d_'42''45'isCommutativeMonoid_3238 (coe v3))))
            (coe
               MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'737''8658'distr_556
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_202
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_496
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                           (coe d_'43''45'isCommutativeMonoid_3236 (coe v3))))))
               (coe v1) (coe v0)
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_496
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                           (coe d_'43''45'isCommutativeMonoid_3236 (coe v3))))))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_comm_776
                  (coe d_'42''45'isCommutativeMonoid_3238 (coe v3)))
               (coe d_distrib'737'_3240 (coe v3))))
         (coe
            MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'691''8658'ze_396
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                        (coe d_'43''45'isCommutativeMonoid_3236 (coe v3))))))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Structures.d_comm_776
               (coe d_'42''45'isCommutativeMonoid_3238 (coe v3)))
            (coe v2) (coe d_zero'691'_3242 (coe v3))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_776
         (coe d_'42''45'isCommutativeMonoid_3238 (coe v3)))
-- Algebra.Structures.Biased.IsRing*
d_IsRing'42'_3350 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsRing'42'_3350
  = C_constructor_3420 MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
                       MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.Biased.IsRing*.+-isAbelianGroup
d_'43''45'isAbelianGroup_3370 ::
  T_IsRing'42'_3350 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_3370 v0
  = case coe v0 of
      C_constructor_3420 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRing*.*-isMonoid
d_'42''45'isMonoid_3372 ::
  T_IsRing'42'_3350 -> MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_3372 v0
  = case coe v0 of
      C_constructor_3420 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRing*.distrib
d_distrib_3374 ::
  T_IsRing'42'_3350 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_3374 v0
  = case coe v0 of
      C_constructor_3420 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRing*.zero
d_zero_3376 ::
  T_IsRing'42'_3350 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_3376 v0
  = case coe v0 of
      C_constructor_3420 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRing*.isRing
d_isRing_3378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3350 -> MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_isRing_3378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isRing_3378 v9
du_isRing_3378 ::
  T_IsRing'42'_3350 -> MAlonzo.Code.Algebra.Structures.T_IsRing_2740
du_isRing_3378 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_2876
      (coe d_'43''45'isAbelianGroup_3370 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe d_'42''45'isMonoid_3372 (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe d_'42''45'isMonoid_3372 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_724
         (coe d_'42''45'isMonoid_3372 (coe v0)))
      (coe d_distrib_3374 (coe v0))
-- Algebra.Structures.Biased.IsRing*._._.identityʳ
d_identity'691'_3390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing'42'_3350 -> AgdaAny -> AgdaAny
d_identity'691'_3390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_3390 v9
du_identity'691'_3390 :: T_IsRing'42'_3350 -> AgdaAny -> AgdaAny
du_identity'691'_3390 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'691'_754
      (coe d_'42''45'isMonoid_3372 (coe v0))
-- Algebra.Structures.Biased.IsRing*._._.identityˡ
d_identity'737'_3392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing'42'_3350 -> AgdaAny -> AgdaAny
d_identity'737'_3392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_3392 v9
du_identity'737'_3392 :: T_IsRing'42'_3350 -> AgdaAny -> AgdaAny
du_identity'737'_3392 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'737'_752
      (coe d_'42''45'isMonoid_3372 (coe v0))
-- Algebra.Structures.Biased.IsRing*._._.isPartialEquivalence
d_isPartialEquivalence_3398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3350 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_3398 v9
du_isPartialEquivalence_3398 ::
  T_IsRing'42'_3350 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3398 v0
  = let v1 = d_'42''45'isMonoid_3372 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.Biased.IsRing*._._.isUnitalMagma
d_isUnitalMagma_3402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3350 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_3402 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_3402 v9
du_isUnitalMagma_3402 ::
  T_IsRing'42'_3350 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_3402 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe d_'42''45'isMonoid_3372 (coe v0))
-- Algebra.Structures.Biased.IsRing*._._.reflexive
d_reflexive_3406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3350 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_3406 v9
du_reflexive_3406 ::
  T_IsRing'42'_3350 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3406 v0
  = let v1 = d_'42''45'isMonoid_3372 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3))
                 v4)))
-- Algebra.Structures.Biased.IsRing*._._.setoid
d_setoid_3408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3350 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_3408 v9
du_setoid_3408 ::
  T_IsRing'42'_3350 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3408 v0
  = let v1 = d_'42''45'isMonoid_3372 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Algebra.Structures.Biased.IsRing*._._.∙-congʳ
d_'8729''45'cong'691'_3416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_3416 v9
du_'8729''45'cong'691'_3416 ::
  T_IsRing'42'_3350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3416 v0
  = let v1 = d_'42''45'isMonoid_3372 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.Biased.IsRing*._._.∙-congˡ
d_'8729''45'cong'737'_3418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_3418 v9
du_'8729''45'cong'737'_3418 ::
  T_IsRing'42'_3350 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3418 v0
  = let v1 = d_'42''45'isMonoid_3372 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero
d_IsRingWithoutAnnihilatingZero_3432 a0 a1 a2 a3 a4 a5 a6 a7 a8
  = ()
data T_IsRingWithoutAnnihilatingZero_3432
  = C_constructor_3566 MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
                       MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+-isAbelianGroup
d_'43''45'isAbelianGroup_3450 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_3450 v0
  = case coe v0 of
      C_constructor_3566 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*-isMonoid
d_'42''45'isMonoid_3452 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_3452 v0
  = case coe v0 of
      C_constructor_3566 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.distrib
d_distrib_3454 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_3454 v0
  = case coe v0 of
      C_constructor_3566 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+._//_
d__'47''47'__3458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__3458 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du__'47''47'__3458 v4 v6
du__'47''47'__3458 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__3458 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.assoc
d_assoc_3460 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_3460 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe d_'43''45'isAbelianGroup_3450 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.comm
d_comm_3462 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_3462 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_1186
      (coe d_'43''45'isAbelianGroup_3450 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.identity
d_identity_3464 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3464 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe d_'43''45'isAbelianGroup_3450 (coe v0))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.identityʳ
d_identity'691'_3466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_identity'691'_3466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_3466 v9
du_identity'691'_3466 ::
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
du_identity'691'_3466 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_754
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.identityˡ
d_identity'737'_3468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_identity'737'_3468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_3468 v9
du_identity'737'_3468 ::
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
du_identity'737'_3468 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_752
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.inverse
d_inverse_3470 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_3470 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe d_'43''45'isAbelianGroup_3450 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.inverseʳ
d_inverse'691'_3472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_inverse'691'_3472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'691'_3472 v9
du_inverse'691'_3472 ::
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
du_inverse'691'_3472 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_inverse'691'_1146
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.inverseˡ
d_inverse'737'_3474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_inverse'737'_3474 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'737'_3474 v9
du_inverse'737'_3474 ::
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
du_inverse'737'_3474 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_inverse'737'_1144
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isCommutativeMagma
d_isCommutativeMagma_3476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_3476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_3476 v9
du_isCommutativeMagma_3476 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_3476 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
               (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isCommutativeMonoid
d_isCommutativeMonoid_3478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_3478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMonoid_3478 v9
du_isCommutativeMonoid_3478 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_3478 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
      (coe d_'43''45'isAbelianGroup_3450 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isCommutativeSemigroup
d_isCommutativeSemigroup_3480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_3480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_3480 v9
du_isCommutativeSemigroup_3480 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_3480 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
            (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isEquivalence
d_isEquivalence_3482 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3482 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                  (coe d_'43''45'isAbelianGroup_3450 (coe v0))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isGroup
d_isGroup_3484 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_3484 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe d_'43''45'isAbelianGroup_3450 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isInvertibleMagma
d_isInvertibleMagma_3486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_3486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isInvertibleMagma_3486 v9
du_isInvertibleMagma_3486 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_3486 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_3488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_3488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_isInvertibleUnitalMagma_3488 v9
du_isInvertibleUnitalMagma_3488 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_3488 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isMagma
d_isMagma_3490 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_3490 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe d_'43''45'isAbelianGroup_3450 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isMonoid
d_isMonoid_3492 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_3492 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe d_'43''45'isAbelianGroup_3450 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isPartialEquivalence
d_isPartialEquivalence_3494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_3494 v9
du_isPartialEquivalence_3494 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3494 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v5)))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isSemigroup
d_isSemigroup_3496 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_3496 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe d_'43''45'isAbelianGroup_3450 (coe v0))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isUnitalMagma
d_isUnitalMagma_3498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_3498 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_3498 v9
du_isUnitalMagma_3498 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_3498 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.refl
d_refl_3500 ::
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_refl_3500 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                     (coe d_'43''45'isAbelianGroup_3450 (coe v0)))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.reflexive
d_reflexive_3502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_3502 v9
du_reflexive_3502 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3502 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v5))
                       v6)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.setoid
d_setoid_3504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_3504 v9
du_setoid_3504 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3504 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.sym
d_sym_3506 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3506 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                     (coe d_'43''45'isAbelianGroup_3450 (coe v0)))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.trans
d_trans_3508 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3508 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                     (coe d_'43''45'isAbelianGroup_3450 (coe v0)))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_3510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_3510 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'691''45''8315''185'_3510 v4 v6 v7 v9
du_unique'691''45''8315''185'_3510 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_3510 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_3450 (coe v3) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1158
         (coe v0) (coe v2) (coe v1)
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v4)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_3512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_3512 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'737''45''8315''185'_3512 v4 v6 v7 v9
du_unique'737''45''8315''185'_3512 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_3512 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_3450 (coe v3) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1152
         (coe v0) (coe v2) (coe v1)
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v4)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.⁻¹-cong
d_'8315''185''45'cong_3514 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_3514 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1092
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe d_'43''45'isAbelianGroup_3450 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.∙-cong
d_'8729''45'cong_3516 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3516 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                  (coe d_'43''45'isAbelianGroup_3450 (coe v0))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.∙-congʳ
d_'8729''45'cong'691'_3518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_3518 v9
du_'8729''45'cong'691'_3518 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3518 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (let v6
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.∙-congˡ
d_'8729''45'cong'737'_3520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_3520 v9
du_'8729''45'cong'737'_3520 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3520 v0
  = let v1 = d_'43''45'isAbelianGroup_3450 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (let v6
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.assoc
d_assoc_3524 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_3524 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe d_'42''45'isMonoid_3452 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.identity
d_identity_3526 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3526 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe d_'42''45'isMonoid_3452 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.identityʳ
d_identity'691'_3528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_identity'691'_3528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_3528 v9
du_identity'691'_3528 ::
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
du_identity'691'_3528 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'691'_754
      (coe d_'42''45'isMonoid_3452 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.identityˡ
d_identity'737'_3530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_identity'737'_3530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_3530 v9
du_identity'737'_3530 ::
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
du_identity'737'_3530 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'737'_752
      (coe d_'42''45'isMonoid_3452 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isEquivalence
d_isEquivalence_3532 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3532 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe d_'42''45'isMonoid_3452 (coe v0))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isMagma
d_isMagma_3534 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_3534 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe d_'42''45'isMonoid_3452 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isPartialEquivalence
d_isPartialEquivalence_3536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_3536 v9
du_isPartialEquivalence_3536 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3536 v0
  = let v1 = d_'42''45'isMonoid_3452 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isSemigroup
d_isSemigroup_3538 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_3538 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe d_'42''45'isMonoid_3452 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isUnitalMagma
d_isUnitalMagma_3540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_3540 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_3540 v9
du_isUnitalMagma_3540 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_3540 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe d_'42''45'isMonoid_3452 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.refl
d_refl_3542 ::
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_refl_3542 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe d_'42''45'isMonoid_3452 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.reflexive
d_reflexive_3544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_3544 v9
du_reflexive_3544 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3544 v0
  = let v1 = d_'42''45'isMonoid_3452 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3))
                 v4)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.setoid
d_setoid_3546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_3546 v9
du_setoid_3546 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3546 v0
  = let v1 = d_'42''45'isMonoid_3452 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.sym
d_sym_3548 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3548 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe d_'42''45'isMonoid_3452 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.trans
d_trans_3550 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3550 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe d_'42''45'isMonoid_3452 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.∙-cong
d_'8729''45'cong_3552 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3552 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe d_'42''45'isMonoid_3452 (coe v0))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.∙-congʳ
d_'8729''45'cong'691'_3554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_3554 v9
du_'8729''45'cong'691'_3554 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3554 v0
  = let v1 = d_'42''45'isMonoid_3452 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.∙-congˡ
d_'8729''45'cong'737'_3556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_3556 v9
du_'8729''45'cong'737'_3556 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3556 v0
  = let v1 = d_'42''45'isMonoid_3452 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                           (coe v4))))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.zeroˡ
d_zero'737'_3558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_zero'737'_3558 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'737'_3558 v4 v5 v6 v7 v9
du_zero'737'_3558 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
du_zero'737'_3558 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'distrib'691''8743'id'691''8743'inv'691''8658'ze'737'_644
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                     (coe d_'43''45'isAbelianGroup_3450 (coe v4)))))))
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                     (coe d_'43''45'isAbelianGroup_3450 (coe v4)))))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe d_'42''45'isMonoid_3452 (coe v4)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                  (coe d_'43''45'isAbelianGroup_3450 (coe v4))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_distrib_3454 (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_754
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe d_'43''45'isAbelianGroup_3450 (coe v4)))))
      (coe
         MAlonzo.Code.Algebra.Structures.du_inverse'691'_1146
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe d_'43''45'isAbelianGroup_3450 (coe v4))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.zeroʳ
d_zero'691'_3560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
d_zero'691'_3560 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'691'_3560 v4 v5 v6 v7 v9
du_zero'691'_3560 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 -> AgdaAny -> AgdaAny
du_zero'691'_3560 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'distrib'737''8743'id'691''8743'inv'691''8658'ze'691'_656
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                     (coe d_'43''45'isAbelianGroup_3450 (coe v4)))))))
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                     (coe d_'43''45'isAbelianGroup_3450 (coe v4)))))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe d_'42''45'isMonoid_3452 (coe v4)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                  (coe d_'43''45'isAbelianGroup_3450 (coe v4))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_distrib_3454 (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_754
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe d_'43''45'isAbelianGroup_3450 (coe v4)))))
      (coe
         MAlonzo.Code.Algebra.Structures.du_inverse'691'_1146
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe d_'43''45'isAbelianGroup_3450 (coe v4))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.zero
d_zero_3562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_3562 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero_3562 v4 v5 v6 v7 v9
du_zero_3562 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_3562 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_zero'737'_3558 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         du_zero'691'_3560 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.isRing
d_isRing_3564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_isRing_3564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isRing_3564 v9
du_isRing_3564 ::
  T_IsRingWithoutAnnihilatingZero_3432 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
du_isRing_3564 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_2876
      (coe d_'43''45'isAbelianGroup_3450 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe d_'42''45'isMonoid_3452 (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe d_'42''45'isMonoid_3452 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_724
         (coe d_'42''45'isMonoid_3452 (coe v0)))
      (coe d_distrib_3454 (coe v0))
