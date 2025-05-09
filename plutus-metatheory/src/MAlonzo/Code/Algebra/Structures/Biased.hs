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

module MAlonzo.Code.Algebra.Structures.Biased where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Consequences.Setoid qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
d_IsCommutativeMonoid_158 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Structures.Biased._.IsCommutativeSemiring
d_IsCommutativeSemiring_164 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Structures.Biased._.IsMonoid
d_IsMonoid_196 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Structures.Biased._.IsNearSemiring
d_IsNearSemiring_200 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Structures.Biased._.IsRing
d_IsRing_212 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Algebra.Structures.Biased._.IsSemigroup
d_IsSemigroup_218 a0 a1 a2 a3 a4 = ()
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_224 a0 a1 a2 a3 a4 a5 a6 a7
  = ()
-- Algebra.Structures.Biased._.IsSemiringWithoutOne
d_IsSemiringWithoutOne_226 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Structures.Biased._.IsAbelianGroup._//_
d__'47''47'__234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__234 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7
  = du__'47''47'__234 v4 v6
du__'47''47'__234 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__234 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1098 (coe v0)
      (coe v1)
-- Algebra.Structures.Biased._.IsAbelianGroup.comm
d_comm_238 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_238 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_1146 (coe v0)
-- Algebra.Structures.Biased._.IsAbelianGroup.identityʳ
d_identity'691'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny
d_identity'691'_242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'691'_242 v7
du_identity'691'_242 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny
du_identity'691'_242 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_728
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1)))
-- Algebra.Structures.Biased._.IsAbelianGroup.identityˡ
d_identity'737'_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny
d_identity'737'_244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_identity'737'_244 v7
du_identity'737'_244 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny
du_identity'737'_244 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'737'_726
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1)))
-- Algebra.Structures.Biased._.IsAbelianGroup.inverseʳ
d_inverse'691'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny
d_inverse'691'_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'691'_248 v7
du_inverse'691'_248 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny
du_inverse'691'_248 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.inverseˡ
d_inverse'737'_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny
d_inverse'737'_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_inverse'737'_250 v7
du_inverse'737'_250 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny
du_inverse'737'_250 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_inverse'737'_1106
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.isCommutativeMagma
d_isCommutativeMagma_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212
d_isCommutativeMagma_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeMagma_252 v7
du_isCommutativeMagma_252 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212
du_isCommutativeMagma_252 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1204
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_586
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_786
            (coe v1)))
-- Algebra.Structures.Biased._.IsAbelianGroup.isCommutativeMonoid
d_isCommutativeMonoid_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_isCommutativeMonoid_254 ~v0 ~v1 ~v2 ~v3
  = du_isCommutativeMonoid_254
du_isCommutativeMonoid_254 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_isCommutativeMonoid_254 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1204 v3
-- Algebra.Structures.Biased._.IsAbelianGroup.isCommutativeSemigroup
d_isCommutativeSemigroup_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isCommutativeSemigroup_256 v7
du_isCommutativeSemigroup_256 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_786
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1204
         (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.isGroup
d_isGroup_260 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_260 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)
-- Algebra.Structures.Biased._.IsAbelianGroup.isInvertibleMagma
d_isInvertibleMagma_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924
d_isInvertibleMagma_262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleMagma_262 v7
du_isInvertibleMagma_262 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924
du_isInvertibleMagma_262 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1122
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976
d_isInvertibleUnitalMagma_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isInvertibleUnitalMagma_264 v7
du_isInvertibleUnitalMagma_264 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976
du_isInvertibleUnitalMagma_264 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1124
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))
-- Algebra.Structures.Biased._.IsAbelianGroup.isPartialEquivalence
d_isPartialEquivalence_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_270 v7
du_isPartialEquivalence_270 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_270 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))))
-- Algebra.Structures.Biased._.IsAbelianGroup.isUnitalMagma
d_isUnitalMagma_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
d_isUnitalMagma_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnitalMagma_274 v7
du_isUnitalMagma_274 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
du_isUnitalMagma_274 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_730
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1)))
-- Algebra.Structures.Biased._.IsAbelianGroup.reflexive
d_reflexive_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_278 v7
du_reflexive_278 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_278 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                    v5))))
-- Algebra.Structures.Biased._.IsAbelianGroup.setoid
d_setoid_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_280 v7
du_setoid_280 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_280 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_200
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Structures.Biased._.IsAbelianGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_286 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'691''45''8315''185'_286 v4 v5 v6 v7
du_unique'691''45''8315''185'_286 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_286 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1120
      (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3))
-- Algebra.Structures.Biased._.IsAbelianGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_288 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_unique'737''45''8315''185'_288 v4 v5 v6 v7
du_unique'737''45''8315''185'_288 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_288 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1114
      (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3))
-- Algebra.Structures.Biased._.IsAbelianGroup.∙-congʳ
d_'8729''45'cong'691'_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'691'_294 v7
du_'8729''45'cong'691'_294 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_294 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Structures.Biased._.IsAbelianGroup.∙-congˡ
d_'8729''45'cong'737'_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8729''45'cong'737'_296 v7
du_'8729''45'cong'737'_296 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_296 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Structures.Biased._.IsCommutativeMonoid.comm
d_comm_528 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_528 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_748 (coe v0)
-- Algebra.Structures.Biased._.IsCommutativeMonoid.isMonoid
d_isMonoid_544 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_544 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0)
-- Algebra.Structures.Biased._.IsCommutativeSemiring.*-comm
d_'42''45'comm_728 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_728 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1694 (coe v0)
-- Algebra.Structures.Biased._.IsCommutativeSemiring.isSemiring
d_isSemiring_798 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_798 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)
-- Algebra.Structures.Biased._.IsMonoid.identity
d_identity_1600 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1600 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_698 (coe v0)
-- Algebra.Structures.Biased._.IsMonoid.identityʳ
d_identity'691'_1602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny -> AgdaAny
d_identity'691'_1602 ~v0 ~v1 ~v2 ~v3 = du_identity'691'_1602
du_identity'691'_1602 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny -> AgdaAny
du_identity'691'_1602 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_identity'691'_728 v2
-- Algebra.Structures.Biased._.IsMonoid.identityˡ
d_identity'737'_1604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny -> AgdaAny
d_identity'737'_1604 ~v0 ~v1 ~v2 ~v3 = du_identity'737'_1604
du_identity'737'_1604 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny -> AgdaAny
du_identity'737'_1604 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_identity'737'_726 v2
-- Algebra.Structures.Biased._.IsMonoid.isPartialEquivalence
d_isPartialEquivalence_1610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_1610 v6
du_isPartialEquivalence_1610 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1610 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v2))))
-- Algebra.Structures.Biased._.IsMonoid.isSemigroup
d_isSemigroup_1612 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1612 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0)
-- Algebra.Structures.Biased._.IsMonoid.isUnitalMagma
d_isUnitalMagma_1614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
d_isUnitalMagma_1614 ~v0 ~v1 ~v2 ~v3 = du_isUnitalMagma_1614
du_isUnitalMagma_1614 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
du_isUnitalMagma_1614 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_730 v2
-- Algebra.Structures.Biased._.IsMonoid.reflexive
d_reflexive_1618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_1618 v6
du_reflexive_1618 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1618 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v2))
              v3))
-- Algebra.Structures.Biased._.IsMonoid.setoid
d_setoid_1620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_1620 v6
du_setoid_1620 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1620 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_200
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v1)))
-- Algebra.Structures.Biased._.IsMonoid.∙-congʳ
d_'8729''45'cong'691'_1628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1628 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_1628 v6
du_'8729''45'cong'691'_1628 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1628 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v1)))
-- Algebra.Structures.Biased._.IsMonoid.∙-congˡ
d_'8729''45'cong'737'_1630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_1630 v6
du_'8729''45'cong'737'_1630 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1630 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v1)))
-- Algebra.Structures.Biased._.IsNearSemiring.*-assoc
d_'42''45'assoc_1700 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_1700 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1240 (coe v0)
-- Algebra.Structures.Biased._.IsNearSemiring.*-cong
d_'42''45'cong_1702 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_1702 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1238 (coe v0)
-- Algebra.Structures.Biased._.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1728 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'isMonoid_1728 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0)
-- Algebra.Structures.Biased._.IsNearSemiring.distribʳ
d_distrib'691'_1734 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_1734 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib'691'_1242 (coe v0)
-- Algebra.Structures.Biased._.IsNearSemiring.zeroˡ
d_zero'737'_1750 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  AgdaAny -> AgdaAny
d_zero'737'_1750 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero'737'_1244 (coe v0)
-- Algebra.Structures.Biased._.IsRing.*-assoc
d_'42''45'assoc_2118 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2118 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2676 (coe v0)
-- Algebra.Structures.Biased._.IsRing.*-cong
d_'42''45'cong_2120 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2120 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_2674 (coe v0)
-- Algebra.Structures.Biased._.IsRing.*-identity
d_'42''45'identity_2126 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2126 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2678 (coe v0)
-- Algebra.Structures.Biased._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2154 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
      (coe v0)
-- Algebra.Structures.Biased._.IsRing.distrib
d_distrib_2184 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2184 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2680 (coe v0)
-- Algebra.Structures.Biased._.IsSemigroup.assoc
d_assoc_2344 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2344 v0
  = coe MAlonzo.Code.Algebra.Structures.d_assoc_482 (coe v0)
-- Algebra.Structures.Biased._.IsSemigroup.isMagma
d_isMagma_2348 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2348 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2484 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2484 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1492 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2486 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2486 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1490 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2492 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2492 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2522 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2522 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2534 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2534 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1496 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2560 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2560 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_1320 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2562 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2562 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1318 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2576 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2576 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
      (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.distrib
d_distrib_2584 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2584 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1322 (coe v0)
-- Algebra.Structures.Biased._.IsSemiringWithoutOne.zero
d_zero_2604 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2604 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1324 (coe v0)
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ
d_IsCommutativeMonoid'737'_2662 a0 a1 a2 a3 a4 a5 = ()
data T_IsCommutativeMonoid'737'_2662
  = C_IsCommutativeMonoid'737''46'constructor_34899 MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
                                                    (AgdaAny -> AgdaAny)
                                                    (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ.isSemigroup
d_isSemigroup_2674 ::
  T_IsCommutativeMonoid'737'_2662 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2674 v0
  = case coe v0 of
      C_IsCommutativeMonoid'737''46'constructor_34899 v1 v2 v3 -> coe v1
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ.identityˡ
d_identity'737'_2676 ::
  T_IsCommutativeMonoid'737'_2662 -> AgdaAny -> AgdaAny
d_identity'737'_2676 v0
  = case coe v0 of
      C_IsCommutativeMonoid'737''46'constructor_34899 v1 v2 v3 -> coe v2
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ.comm
d_comm_2678 ::
  T_IsCommutativeMonoid'737'_2662 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2678 v0
  = case coe v0 of
      C_IsCommutativeMonoid'737''46'constructor_34899 v1 v2 v3 -> coe v3
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidˡ.isCommutativeMonoid
d_isCommutativeMonoid_2680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid'737'_2662 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_isCommutativeMonoid_2680 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCommutativeMonoid_2680 v4 v5 v6
du_isCommutativeMonoid_2680 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid'737'_2662 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_isCommutativeMonoid_2680 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
         (coe d_isSemigroup_2674 (coe v2))
         (coe
            MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'id'737''8658'id_352
            (let v3 = d_isSemigroup_2674 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3))))
            (coe v0) (coe d_comm_2678 (coe v2)) (coe v1)
            (coe d_identity'737'_2676 (coe v2))))
      (coe d_comm_2678 (coe v2))
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ
d_IsCommutativeMonoid'691'_2716 a0 a1 a2 a3 a4 a5 = ()
data T_IsCommutativeMonoid'691'_2716
  = C_IsCommutativeMonoid'691''46'constructor_36341 MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
                                                    (AgdaAny -> AgdaAny)
                                                    (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ.isSemigroup
d_isSemigroup_2728 ::
  T_IsCommutativeMonoid'691'_2716 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2728 v0
  = case coe v0 of
      C_IsCommutativeMonoid'691''46'constructor_36341 v1 v2 v3 -> coe v1
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ.identityʳ
d_identity'691'_2730 ::
  T_IsCommutativeMonoid'691'_2716 -> AgdaAny -> AgdaAny
d_identity'691'_2730 v0
  = case coe v0 of
      C_IsCommutativeMonoid'691''46'constructor_36341 v1 v2 v3 -> coe v2
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ.comm
d_comm_2732 ::
  T_IsCommutativeMonoid'691'_2716 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_2732 v0
  = case coe v0 of
      C_IsCommutativeMonoid'691''46'constructor_36341 v1 v2 v3 -> coe v3
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeMonoidʳ.isCommutativeMonoid
d_isCommutativeMonoid_2734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid'691'_2716 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_isCommutativeMonoid_2734 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCommutativeMonoid_2734 v4 v5 v6
du_isCommutativeMonoid_2734 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeMonoid'691'_2716 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_isCommutativeMonoid_2734 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
         (coe d_isSemigroup_2728 (coe v2))
         (coe
            MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'id'691''8658'id_356
            (let v3 = d_isSemigroup_2728 (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3))))
            (coe v0) (coe d_comm_2732 (coe v2)) (coe v1)
            (coe d_identity'691'_2730 (coe v2))))
      (coe d_comm_2732 (coe v2))
-- Algebra.Structures.Biased.IsSemiringWithoutOne*
d_IsSemiringWithoutOne'42'_2772 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsSemiringWithoutOne'42'_2772
  = C_IsSemiringWithoutOne'42''46'constructor_37821 MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
                                                    MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
                                                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2788 ::
  T_IsSemiringWithoutOne'42'_2772 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2788 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'42''46'constructor_37821 v1 v2 v3 v4
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.*-isSemigroup
d_'42''45'isSemigroup_2790 ::
  T_IsSemiringWithoutOne'42'_2772 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'42''45'isSemigroup_2790 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'42''46'constructor_37821 v1 v2 v3 v4
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.distrib
d_distrib_2792 ::
  T_IsSemiringWithoutOne'42'_2772 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2792 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'42''46'constructor_37821 v1 v2 v3 v4
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.zero
d_zero_2794 ::
  T_IsSemiringWithoutOne'42'_2772 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2794 v0
  = case coe v0 of
      C_IsSemiringWithoutOne'42''46'constructor_37821 v1 v2 v3 v4
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutOne*.isSemiringWithoutOne
d_isSemiringWithoutOne_2796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsSemiringWithoutOne'42'_2772 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_2796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isSemiringWithoutOne_2796 v7
du_isSemiringWithoutOne_2796 ::
  T_IsSemiringWithoutOne'42'_2772 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298
du_isSemiringWithoutOne_2796 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutOne'46'constructor_37629
      (coe d_'43''45'isCommutativeMonoid_2788 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe d_'42''45'isSemigroup_2790 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe d_'42''45'isSemigroup_2790 (coe v0)))
      (coe d_distrib_2792 (coe v0)) (coe d_zero_2794 (coe v0))
-- Algebra.Structures.Biased.IsNearSemiring*
d_IsNearSemiring'42'_2834 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsNearSemiring'42'_2834
  = C_IsNearSemiring'42''46'constructor_39635 MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
                                              MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
                                              (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                              (AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsNearSemiring*.+-isMonoid
d_'43''45'isMonoid_2850 ::
  T_IsNearSemiring'42'_2834 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'isMonoid_2850 v0
  = case coe v0 of
      C_IsNearSemiring'42''46'constructor_39635 v1 v2 v3 v4 -> coe v1
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsNearSemiring*.*-isSemigroup
d_'42''45'isSemigroup_2852 ::
  T_IsNearSemiring'42'_2834 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'42''45'isSemigroup_2852 v0
  = case coe v0 of
      C_IsNearSemiring'42''46'constructor_39635 v1 v2 v3 v4 -> coe v2
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsNearSemiring*.distribʳ
d_distrib'691'_2854 ::
  T_IsNearSemiring'42'_2834 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2854 v0
  = case coe v0 of
      C_IsNearSemiring'42''46'constructor_39635 v1 v2 v3 v4 -> coe v3
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsNearSemiring*.zeroˡ
d_zero'737'_2856 :: T_IsNearSemiring'42'_2834 -> AgdaAny -> AgdaAny
d_zero'737'_2856 v0
  = case coe v0 of
      C_IsNearSemiring'42''46'constructor_39635 v1 v2 v3 v4 -> coe v4
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsNearSemiring*.isNearSemiring
d_isNearSemiring_2858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsNearSemiring'42'_2834 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218
d_isNearSemiring_2858 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isNearSemiring_2858 v7
du_isNearSemiring_2858 ::
  T_IsNearSemiring'42'_2834 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218
du_isNearSemiring_2858 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsNearSemiring'46'constructor_35025
      (coe d_'43''45'isMonoid_2850 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe d_'42''45'isSemigroup_2852 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe d_'42''45'isSemigroup_2852 (coe v0)))
      (coe d_distrib'691'_2854 (coe v0)) (coe d_zero'737'_2856 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*
d_IsSemiringWithoutAnnihilatingZero'42'_2898 a0 a1 a2 a3 a4 a5 a6
                                             a7
  = ()
data T_IsSemiringWithoutAnnihilatingZero'42'_2898
  = C_IsSemiringWithoutAnnihilatingZero'42''46'constructor_41443 MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
                                                                 MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2914 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2914 v0
  = case coe v0 of
      C_IsSemiringWithoutAnnihilatingZero'42''46'constructor_41443 v1 v2 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*.*-isMonoid
d_'42''45'isMonoid_2916 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'42''45'isMonoid_2916 v0
  = case coe v0 of
      C_IsSemiringWithoutAnnihilatingZero'42''46'constructor_41443 v1 v2 v3
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*.distrib
d_distrib_2918 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2918 v0
  = case coe v0 of
      C_IsSemiringWithoutAnnihilatingZero'42''46'constructor_41443 v1 v2 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2920 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 v8
  = du_isSemiringWithoutAnnihilatingZero_2920 v8
du_isSemiringWithoutAnnihilatingZero_2920 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
du_isSemiringWithoutAnnihilatingZero_2920 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811
      (coe d_'43''45'isCommutativeMonoid_2914 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe d_'42''45'isMonoid_2916 (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe d_'42''45'isMonoid_2916 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_698
         (coe d_'42''45'isMonoid_2916 (coe v0)))
      (coe d_distrib_2918 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.identityʳ
d_identity'691'_2932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 -> AgdaAny -> AgdaAny
d_identity'691'_2932 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'691'_2932 v8
du_identity'691'_2932 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 -> AgdaAny -> AgdaAny
du_identity'691'_2932 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'691'_728
      (coe d_'42''45'isMonoid_2916 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.identityˡ
d_identity'737'_2934 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 -> AgdaAny -> AgdaAny
d_identity'737'_2934 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_identity'737'_2934 v8
du_identity'737'_2934 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 -> AgdaAny -> AgdaAny
du_identity'737'_2934 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'737'_726
      (coe d_'42''45'isMonoid_2916 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.isPartialEquivalence
d_isPartialEquivalence_2940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_2940 v8
du_isPartialEquivalence_2940 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2940 v0
  = let v1 = d_'42''45'isMonoid_2916 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.isUnitalMagma
d_isUnitalMagma_2944 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
d_isUnitalMagma_2944 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isUnitalMagma_2944 v8
du_isUnitalMagma_2944 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
du_isUnitalMagma_2944 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_730
      (coe d_'42''45'isMonoid_2916 (coe v0))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.reflexive
d_reflexive_2948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2948 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_2948 v8
du_reflexive_2948 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2948 v0
  = let v1 = d_'42''45'isMonoid_2916 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3))
                 v4)))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.setoid
d_setoid_2950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2950 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_2950 v8
du_setoid_2950 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2950 v0
  = let v1 = d_'42''45'isMonoid_2916 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_200
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.∙-congʳ
d_'8729''45'cong'691'_2958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'691'_2958 v8
du_'8729''45'cong'691'_2958 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2958 v0
  = let v1 = d_'42''45'isMonoid_2916 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsSemiringWithoutAnnihilatingZero*._._.∙-congˡ
d_'8729''45'cong'737'_2960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8729''45'cong'737'_2960 v8
du_'8729''45'cong'737'_2960 ::
  T_IsSemiringWithoutAnnihilatingZero'42'_2898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2960 v0
  = let v1 = d_'42''45'isMonoid_2916 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ
d_IsCommutativeSemiring'737'_2970 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsCommutativeSemiring'737'_2970
  = C_IsCommutativeSemiring'737''46'constructor_43731 MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
                                                      MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
                                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                      (AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2988 ::
  T_IsCommutativeSemiring'737'_2970 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2988 v0
  = case coe v0 of
      C_IsCommutativeSemiring'737''46'constructor_43731 v1 v2 v3 v4
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_2990 ::
  T_IsCommutativeSemiring'737'_2970 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'42''45'isCommutativeMonoid_2990 v0
  = case coe v0 of
      C_IsCommutativeSemiring'737''46'constructor_43731 v1 v2 v3 v4
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.distribʳ
d_distrib'691'_2992 ::
  T_IsCommutativeSemiring'737'_2970 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_2992 v0
  = case coe v0 of
      C_IsCommutativeSemiring'737''46'constructor_43731 v1 v2 v3 v4
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.zeroˡ
d_zero'737'_2994 ::
  T_IsCommutativeSemiring'737'_2970 -> AgdaAny -> AgdaAny
d_zero'737'_2994 v0
  = case coe v0 of
      C_IsCommutativeSemiring'737''46'constructor_43731 v1 v2 v3 v4
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringˡ.isCommutativeSemiring
d_isCommutativeSemiring_2996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring'737'_2970 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_isCommutativeSemiring_2996 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 v8
  = du_isCommutativeSemiring_2996 v4 v5 v6 v8
du_isCommutativeSemiring_2996 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiring'737'_2970 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
du_isCommutativeSemiring_2996 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51895
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_48071
         (coe
            MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811
            (coe d_'43''45'isCommutativeMonoid_2988 (coe v3))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                        (coe d_'42''45'isCommutativeMonoid_2990 (coe v3))))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_482
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                     (coe d_'42''45'isCommutativeMonoid_2990 (coe v3)))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_identity_698
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                  (coe d_'42''45'isCommutativeMonoid_2990 (coe v3))))
            (coe
               MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'691''8658'distr_528
               (let v4 = d_'43''45'isCommutativeMonoid_2988 (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v4) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))
               (coe v1) (coe v0)
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_480
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                           (coe d_'43''45'isCommutativeMonoid_2988 (coe v3))))))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_comm_748
                  (coe d_'42''45'isCommutativeMonoid_2990 (coe v3)))
               (coe d_distrib'691'_2992 (coe v3))))
         (coe
            MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'737''8658'ze_372
            (let v4 = d_'43''45'isCommutativeMonoid_2988 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Structures.d_comm_748
               (coe d_'42''45'isCommutativeMonoid_2990 (coe v3)))
            (coe v2) (coe d_zero'737'_2994 (coe v3))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_748
         (coe d_'42''45'isCommutativeMonoid_2990 (coe v3)))
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ
d_IsCommutativeSemiring'691'_3098 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsCommutativeSemiring'691'_3098
  = C_IsCommutativeSemiring'691''46'constructor_48791 MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
                                                      MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
                                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                      (AgdaAny -> AgdaAny)
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_3116 ::
  T_IsCommutativeSemiring'691'_3098 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_3116 v0
  = case coe v0 of
      C_IsCommutativeSemiring'691''46'constructor_48791 v1 v2 v3 v4
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_3118 ::
  T_IsCommutativeSemiring'691'_3098 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'42''45'isCommutativeMonoid_3118 v0
  = case coe v0 of
      C_IsCommutativeSemiring'691''46'constructor_48791 v1 v2 v3 v4
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.distribˡ
d_distrib'737'_3120 ::
  T_IsCommutativeSemiring'691'_3098 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_3120 v0
  = case coe v0 of
      C_IsCommutativeSemiring'691''46'constructor_48791 v1 v2 v3 v4
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.zeroʳ
d_zero'691'_3122 ::
  T_IsCommutativeSemiring'691'_3098 -> AgdaAny -> AgdaAny
d_zero'691'_3122 v0
  = case coe v0 of
      C_IsCommutativeSemiring'691''46'constructor_48791 v1 v2 v3 v4
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsCommutativeSemiringʳ.isCommutativeSemiring
d_isCommutativeSemiring_3124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsCommutativeSemiring'691'_3098 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_isCommutativeSemiring_3124 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 v8
  = du_isCommutativeSemiring_3124 v4 v5 v6 v8
du_isCommutativeSemiring_3124 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsCommutativeSemiring'691'_3098 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
du_isCommutativeSemiring_3124 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51895
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_48071
         (coe
            MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811
            (coe d_'43''45'isCommutativeMonoid_3116 (coe v3))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                        (coe d_'42''45'isCommutativeMonoid_3118 (coe v3))))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_482
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                     (coe d_'42''45'isCommutativeMonoid_3118 (coe v3)))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_identity_698
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                  (coe d_'42''45'isCommutativeMonoid_3118 (coe v3))))
            (coe
               MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'737''8658'distr_524
               (let v4 = d_'43''45'isCommutativeMonoid_3116 (coe v3) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v4) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))
               (coe v1) (coe v0)
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_480
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                           (coe d_'43''45'isCommutativeMonoid_3116 (coe v3))))))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_comm_748
                  (coe d_'42''45'isCommutativeMonoid_3118 (coe v3)))
               (coe d_distrib'737'_3120 (coe v3))))
         (coe
            MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'691''8658'ze_376
            (let v4 = d_'43''45'isCommutativeMonoid_3116 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Structures.d_comm_748
               (coe d_'42''45'isCommutativeMonoid_3118 (coe v3)))
            (coe v2) (coe d_zero'691'_3122 (coe v3))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_748
         (coe d_'42''45'isCommutativeMonoid_3118 (coe v3)))
-- Algebra.Structures.Biased.IsRing*
d_IsRing'42'_3228 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsRing'42'_3228
  = C_IsRing'42''46'constructor_53915 MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
                                      MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
                                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                      MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.Biased.IsRing*.+-isAbelianGroup
d_'43''45'isAbelianGroup_3248 ::
  T_IsRing'42'_3228 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_3248 v0
  = case coe v0 of
      C_IsRing'42''46'constructor_53915 v1 v2 v3 v4 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRing*.*-isMonoid
d_'42''45'isMonoid_3250 ::
  T_IsRing'42'_3228 -> MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'42''45'isMonoid_3250 v0
  = case coe v0 of
      C_IsRing'42''46'constructor_53915 v1 v2 v3 v4 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRing*.distrib
d_distrib_3252 ::
  T_IsRing'42'_3228 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_3252 v0
  = case coe v0 of
      C_IsRing'42''46'constructor_53915 v1 v2 v3 v4 -> coe v3
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRing*.zero
d_zero_3254 ::
  T_IsRing'42'_3228 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_3254 v0
  = case coe v0 of
      C_IsRing'42''46'constructor_53915 v1 v2 v3 v4 -> coe v4
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRing*.isRing
d_isRing_3256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3228 -> MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_isRing_3256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isRing_3256 v9
du_isRing_3256 ::
  T_IsRing'42'_3228 -> MAlonzo.Code.Algebra.Structures.T_IsRing_2650
du_isRing_3256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsRing'46'constructor_95033
      (coe d_'43''45'isAbelianGroup_3248 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe d_'42''45'isMonoid_3250 (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe d_'42''45'isMonoid_3250 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_698
         (coe d_'42''45'isMonoid_3250 (coe v0)))
      (coe d_distrib_3252 (coe v0))
-- Algebra.Structures.Biased.IsRing*._._.identityʳ
d_identity'691'_3268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing'42'_3228 -> AgdaAny -> AgdaAny
d_identity'691'_3268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_3268 v9
du_identity'691'_3268 :: T_IsRing'42'_3228 -> AgdaAny -> AgdaAny
du_identity'691'_3268 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'691'_728
      (coe d_'42''45'isMonoid_3250 (coe v0))
-- Algebra.Structures.Biased.IsRing*._._.identityˡ
d_identity'737'_3270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsRing'42'_3228 -> AgdaAny -> AgdaAny
d_identity'737'_3270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_3270 v9
du_identity'737'_3270 :: T_IsRing'42'_3228 -> AgdaAny -> AgdaAny
du_identity'737'_3270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'737'_726
      (coe d_'42''45'isMonoid_3250 (coe v0))
-- Algebra.Structures.Biased.IsRing*._._.isPartialEquivalence
d_isPartialEquivalence_3276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3228 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_3276 v9
du_isPartialEquivalence_3276 ::
  T_IsRing'42'_3228 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3276 v0
  = let v1 = d_'42''45'isMonoid_3250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.Biased.IsRing*._._.isUnitalMagma
d_isUnitalMagma_3280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3228 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
d_isUnitalMagma_3280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_3280 v9
du_isUnitalMagma_3280 ::
  T_IsRing'42'_3228 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
du_isUnitalMagma_3280 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_730
      (coe d_'42''45'isMonoid_3250 (coe v0))
-- Algebra.Structures.Biased.IsRing*._._.reflexive
d_reflexive_3284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3228 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_3284 v9
du_reflexive_3284 ::
  T_IsRing'42'_3228 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3284 v0
  = let v1 = d_'42''45'isMonoid_3250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3))
                 v4)))
-- Algebra.Structures.Biased.IsRing*._._.setoid
d_setoid_3286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3228 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_3286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_3286 v9
du_setoid_3286 ::
  T_IsRing'42'_3228 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_3286 v0
  = let v1 = d_'42''45'isMonoid_3250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_200
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsRing*._._.∙-congʳ
d_'8729''45'cong'691'_3294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3228 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_3294 v9
du_'8729''45'cong'691'_3294 ::
  T_IsRing'42'_3228 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3294 v0
  = let v1 = d_'42''45'isMonoid_3250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsRing*._._.∙-congˡ
d_'8729''45'cong'737'_3296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRing'42'_3228 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_3296 v9
du_'8729''45'cong'737'_3296 ::
  T_IsRing'42'_3228 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3296 v0
  = let v1 = d_'42''45'isMonoid_3250 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero
d_IsRingWithoutAnnihilatingZero_3308 a0 a1 a2 a3 a4 a5 a6 a7 a8
  = ()
data T_IsRingWithoutAnnihilatingZero_3308
  = C_IsRingWithoutAnnihilatingZero'46'constructor_56523 MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
                                                         MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
                                                         MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+-isAbelianGroup
d_'43''45'isAbelianGroup_3326 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_3326 v0
  = case coe v0 of
      C_IsRingWithoutAnnihilatingZero'46'constructor_56523 v1 v2 v3
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*-isMonoid
d_'42''45'isMonoid_3328 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'42''45'isMonoid_3328 v0
  = case coe v0 of
      C_IsRingWithoutAnnihilatingZero'46'constructor_56523 v1 v2 v3
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.distrib
d_distrib_3330 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_3330 v0
  = case coe v0 of
      C_IsRingWithoutAnnihilatingZero'46'constructor_56523 v1 v2 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+._//_
d__'47''47'__3334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__3334 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du__'47''47'__3334 v4 v6
du__'47''47'__3334 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__3334 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1098 (coe v0)
      (coe v1)
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.assoc
d_assoc_3336 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_3336 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_482
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe d_'43''45'isAbelianGroup_3326 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.comm
d_comm_3338 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_3338 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_1146
      (coe d_'43''45'isAbelianGroup_3326 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.identity
d_identity_3340 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3340 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe d_'43''45'isAbelianGroup_3326 (coe v0))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.identityʳ
d_identity'691'_3342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_identity'691'_3342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_3342 v9
du_identity'691'_3342 ::
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
du_identity'691'_3342 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_728
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.identityˡ
d_identity'737'_3344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_identity'737'_3344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_3344 v9
du_identity'737'_3344 ::
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
du_identity'737'_3344 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_726
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.inverse
d_inverse_3346 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_3346 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe d_'43''45'isAbelianGroup_3326 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.inverseʳ
d_inverse'691'_3348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_inverse'691'_3348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'691'_3348 v9
du_inverse'691'_3348 ::
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
du_inverse'691'_3348 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.inverseˡ
d_inverse'737'_3350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_inverse'737'_3350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_inverse'737'_3350 v9
du_inverse'737'_3350 ::
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
du_inverse'737'_3350 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_inverse'737'_1106
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isCommutativeMagma
d_isCommutativeMagma_3352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212
d_isCommutativeMagma_3352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMagma_3352 v9
du_isCommutativeMagma_3352 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212
du_isCommutativeMagma_3352 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1204
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_586
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_786
               (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isCommutativeMonoid
d_isCommutativeMonoid_3354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_isCommutativeMonoid_3354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isCommutativeMonoid_3354 v9
du_isCommutativeMonoid_3354 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_isCommutativeMonoid_3354 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1204
      (coe d_'43''45'isAbelianGroup_3326 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isCommutativeSemigroup
d_isCommutativeSemigroup_3356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_3356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              v9
  = du_isCommutativeSemigroup_3356 v9
du_isCommutativeSemigroup_3356 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_3356 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_786
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1204
            (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isEquivalence
d_isEquivalence_3358 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3358 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe d_'43''45'isAbelianGroup_3326 (coe v0))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isGroup
d_isGroup_3360 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_3360 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1144
      (coe d_'43''45'isAbelianGroup_3326 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isInvertibleMagma
d_isInvertibleMagma_3362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924
d_isInvertibleMagma_3362 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isInvertibleMagma_3362 v9
du_isInvertibleMagma_3362 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924
du_isInvertibleMagma_3362 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1122
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_3364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976
d_isInvertibleUnitalMagma_3364 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_isInvertibleUnitalMagma_3364 v9
du_isInvertibleUnitalMagma_3364 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976
du_isInvertibleUnitalMagma_3364 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1124
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isMagma
d_isMagma_3366 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_3366 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe d_'43''45'isAbelianGroup_3326 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isMonoid
d_isMonoid_3368 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_3368 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe d_'43''45'isAbelianGroup_3326 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isPartialEquivalence
d_isPartialEquivalence_3370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_3370 v9
du_isPartialEquivalence_3370 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3370 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5)))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isSemigroup
d_isSemigroup_3372 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_3372 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe d_'43''45'isAbelianGroup_3326 (coe v0))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.isUnitalMagma
d_isUnitalMagma_3374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
d_isUnitalMagma_3374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_3374 v9
du_isUnitalMagma_3374 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
du_isUnitalMagma_3374 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_730
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.refl
d_refl_3376 ::
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_refl_3376 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                     (coe d_'43''45'isAbelianGroup_3326 (coe v0)))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.reflexive
d_reflexive_3378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_3378 v9
du_reflexive_3378 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3378 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                       v6)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.setoid
d_setoid_3380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_3380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_3380 v9
du_setoid_3380 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_3380 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.sym
d_sym_3382 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3382 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                     (coe d_'43''45'isAbelianGroup_3326 (coe v0)))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.trans
d_trans_3384 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3384 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                     (coe d_'43''45'isAbelianGroup_3326 (coe v0)))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_3386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_3386 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'691''45''8315''185'_3386 v4 v6 v7 v9
du_unique'691''45''8315''185'_3386 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_3386 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_3326 (coe v3) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1120
         (coe v0) (coe v2) (coe v1)
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v4)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_3388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_3388 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 ~v8
                                  v9
  = du_unique'737''45''8315''185'_3388 v4 v6 v7 v9
du_unique'737''45''8315''185'_3388 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_3388 v0 v1 v2 v3
  = let v4 = d_'43''45'isAbelianGroup_3326 (coe v3) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1114
         (coe v0) (coe v2) (coe v1)
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v4)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.⁻¹-cong
d_'8315''185''45'cong_3390 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_3390 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1054
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe d_'43''45'isAbelianGroup_3326 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.∙-cong
d_'8729''45'cong_3392 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3392 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe d_'43''45'isAbelianGroup_3326 (coe v0))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.∙-congʳ
d_'8729''45'cong'691'_3394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_3394 v9
du_'8729''45'cong'691'_3394 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3394 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.+.∙-congˡ
d_'8729''45'cong'737'_3396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_3396 v9
du_'8729''45'cong'737'_3396 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3396 v0
  = let v1 = d_'43''45'isAbelianGroup_3326 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.assoc
d_assoc_3400 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_3400 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_482
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe d_'42''45'isMonoid_3328 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.identity
d_identity_3402 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3402 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe d_'42''45'isMonoid_3328 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.identityʳ
d_identity'691'_3404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_identity'691'_3404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'691'_3404 v9
du_identity'691'_3404 ::
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
du_identity'691'_3404 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'691'_728
      (coe d_'42''45'isMonoid_3328 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.identityˡ
d_identity'737'_3406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_identity'737'_3406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_identity'737'_3406 v9
du_identity'737'_3406 ::
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
du_identity'737'_3406 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_identity'737'_726
      (coe d_'42''45'isMonoid_3328 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isEquivalence
d_isEquivalence_3408 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3408 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe d_'42''45'isMonoid_3328 (coe v0))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isMagma
d_isMagma_3410 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_3410 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe d_'42''45'isMonoid_3328 (coe v0)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isPartialEquivalence
d_isPartialEquivalence_3412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_3412 v9
du_isPartialEquivalence_3412 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3412 v0
  = let v1 = d_'42''45'isMonoid_3328 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isSemigroup
d_isSemigroup_3414 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_3414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe d_'42''45'isMonoid_3328 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.isUnitalMagma
d_isUnitalMagma_3416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
d_isUnitalMagma_3416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isUnitalMagma_3416 v9
du_isUnitalMagma_3416 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
du_isUnitalMagma_3416 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_730
      (coe d_'42''45'isMonoid_3328 (coe v0))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.refl
d_refl_3418 ::
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_refl_3418 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe d_'42''45'isMonoid_3328 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.reflexive
d_reflexive_3420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_3420 v9
du_reflexive_3420 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3420 v0
  = let v1 = d_'42''45'isMonoid_3328 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3))
                 v4)))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.setoid
d_setoid_3422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_3422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_3422 v9
du_setoid_3422 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_3422 v0
  = let v1 = d_'42''45'isMonoid_3328 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_200
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.sym
d_sym_3424 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3424 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe d_'42''45'isMonoid_3328 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.trans
d_trans_3426 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3426 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe d_'42''45'isMonoid_3328 (coe v0)))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.∙-cong
d_'8729''45'cong_3428 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3428 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe d_'42''45'isMonoid_3328 (coe v0))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.∙-congʳ
d_'8729''45'cong'691'_3430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'691'_3430 v9
du_'8729''45'cong'691'_3430 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3430 v0
  = let v1 = d_'42''45'isMonoid_3328 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.*.∙-congˡ
d_'8729''45'cong'737'_3432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8729''45'cong'737'_3432 v9
du_'8729''45'cong'737'_3432 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3432 v0
  = let v1 = d_'42''45'isMonoid_3328 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v2))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.zeroˡ
d_zero'737'_3434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_zero'737'_3434 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'737'_3434 v4 v5 v6 v7 v9
du_zero'737'_3434 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
du_zero'737'_3434 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'distrib'691''8743'id'691''8743'inv'691''8658'ze'737'_594
      (let v5 = d_'43''45'isAbelianGroup_3326 (coe v4) in
       coe
         (let v6
                = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v5) in
          coe
            (let v7
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v6) in
             coe
               (let v8
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v7) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v8)))))))
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                     (coe d_'43''45'isAbelianGroup_3326 (coe v4)))))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe d_'42''45'isMonoid_3328 (coe v4)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe d_'43''45'isAbelianGroup_3326 (coe v4))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_distrib_3330 (coe v4)))
      (let v5 = d_'43''45'isAbelianGroup_3326 (coe v4) in
       coe
         (let v6
                = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v5) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_identity'691'_728
               (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v6)))))
      (let v5 = d_'43''45'isAbelianGroup_3326 (coe v4) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v5))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.zeroʳ
d_zero'691'_3436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
d_zero'691'_3436 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero'691'_3436 v4 v5 v6 v7 v9
du_zero'691'_3436 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 -> AgdaAny -> AgdaAny
du_zero'691'_3436 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_assoc'8743'distrib'737''8743'id'691''8743'inv'691''8658'ze'691'_606
      (let v5 = d_'43''45'isAbelianGroup_3326 (coe v4) in
       coe
         (let v6
                = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v5) in
          coe
            (let v7
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v6) in
             coe
               (let v8
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v7) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v8)))))))
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                     (coe d_'43''45'isAbelianGroup_3326 (coe v4)))))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe d_'42''45'isMonoid_3328 (coe v4)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe d_'43''45'isAbelianGroup_3326 (coe v4))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_distrib_3330 (coe v4)))
      (let v5 = d_'43''45'isAbelianGroup_3326 (coe v4) in
       coe
         (let v6
                = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v5) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_identity'691'_728
               (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v6)))))
      (let v5 = d_'43''45'isAbelianGroup_3326 (coe v4) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v5))))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.zero
d_zero_3438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_3438 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9
  = du_zero_3438 v4 v5 v6 v7 v9
du_zero_3438 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_3438 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_zero'737'_3434 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         du_zero'691'_3436 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Structures.Biased.IsRingWithoutAnnihilatingZero.isRing
d_isRing_3440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_isRing_3440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isRing_3440 v9
du_isRing_3440 ::
  T_IsRingWithoutAnnihilatingZero_3308 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
du_isRing_3440 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsRing'46'constructor_95033
      (coe d_'43''45'isAbelianGroup_3326 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe d_'42''45'isMonoid_3328 (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe d_'42''45'isMonoid_3328 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_698
         (coe d_'42''45'isMonoid_3328 (coe v0)))
      (coe d_distrib_3330 (coe v0))
