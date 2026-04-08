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

module MAlonzo.Code.Algebra.Lattice.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Lattice.Structures._._Absorbs_
d__Absorbs__16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__Absorbs__16 = erased
-- Algebra.Lattice.Structures._._DistributesOver_
d__DistributesOver__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__18 = erased
-- Algebra.Lattice.Structures._._DistributesOverʳ_
d__DistributesOver'691'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__20 = erased
-- Algebra.Lattice.Structures._._DistributesOverˡ_
d__DistributesOver'737'__22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__22 = erased
-- Algebra.Lattice.Structures._.Absorptive
d_Absorptive_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Absorptive_28 = erased
-- Algebra.Lattice.Structures._.Associative
d_Associative_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Associative_38 = erased
-- Algebra.Lattice.Structures._.Commutative
d_Commutative_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_42 = erased
-- Algebra.Lattice.Structures._.Congruent₁
d_Congruent'8321'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_Congruent'8321'_44 = erased
-- Algebra.Lattice.Structures._.Congruent₂
d_Congruent'8322'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_46 = erased
-- Algebra.Lattice.Structures._.Inverse
d_Inverse_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Inverse_62 = erased
-- Algebra.Lattice.Structures._.LeftCongruent
d_LeftCongruent_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftCongruent_74 = erased
-- Algebra.Lattice.Structures._.LeftInverse
d_LeftInverse_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftInverse_86 = erased
-- Algebra.Lattice.Structures._.RightCongruent
d_RightCongruent_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightCongruent_104 = erased
-- Algebra.Lattice.Structures._.RightInverse
d_RightInverse_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightInverse_116 = erased
-- Algebra.Lattice.Structures._.IsCommutativeBand
d_IsCommutativeBand_162 a0 a1 a2 a3 a4 = ()
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_198 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Lattice.Structures._.IsBand.isPartialEquivalence
d_isPartialEquivalence_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_424 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_424 v5
du_isPartialEquivalence_424 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_424 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Algebra.Lattice.Structures._.IsBand.reflexive
d_reflexive_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_430 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_430 v5
du_reflexive_430 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_430 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))
              v3))
-- Algebra.Lattice.Structures._.IsBand.setoid
d_setoid_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_432 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_432 v5
du_setoid_432 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_432 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Algebra.Lattice.Structures._.IsBand.∙-congʳ
d_'8729''45'cong'691'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_440 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_440 v5
du_'8729''45'cong'691'_440 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_440 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
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
-- Algebra.Lattice.Structures._.IsBand.∙-congˡ
d_'8729''45'cong'737'_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_442 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_442 v5
du_'8729''45'cong'737'_442 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_442 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
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
-- Algebra.Lattice.Structures._.IsCommutativeBand.comm
d_comm_550 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_550 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_622 (coe v0)
-- Algebra.Lattice.Structures._.IsCommutativeBand.isBand
d_isBand_554 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_554 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.idem
d_idem_1072 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_idem_1072 v0
  = coe MAlonzo.Code.Algebra.Structures.d_idem_896 (coe v0)
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.identityʳ
d_identity'691'_1076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_identity'691'_1076 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_1076 v6
du_identity'691'_1076 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_identity'691'_1076 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_754
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.identityˡ
d_identity'737'_1078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_identity'737'_1078 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_1078 v6
du_identity'737'_1078 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_identity'737'_1078 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'737'_752
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.isBand
d_isBand_1080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1080 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isBand_1080 v6
du_isBand_1080 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1080 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.isCommutativeBand
d_isCommutativeBand_1082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1082 ~v0 ~v1 ~v2 ~v3
  = du_isCommutativeBand_1082
du_isCommutativeBand_1082 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_1082 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 v2
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_1084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1084 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeMagma_1084 v6
du_isCommutativeMagma_1084 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1084 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_1086 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_1086 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0)
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_1088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1088 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeSemigroup_1088 v6
du_isCommutativeSemigroup_1088 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1088 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.isIdempotentMonoid
d_isIdempotentMonoid_1092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1092 ~v0 ~v1 ~v2 ~v3
  = du_isIdempotentMonoid_1092
du_isIdempotentMonoid_1092 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_1092 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 v2
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_1098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1098 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_1098 v6
du_isPartialEquivalence_1098 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1098 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
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
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_1102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_1102 v6
du_isUnitalMagma_1102 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1102 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.reflexive
d_reflexive_1106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_1106 v6
du_reflexive_1106 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1106 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
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
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.setoid
d_setoid_1108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_1108 v6
du_setoid_1108 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1108 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_1116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_1116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_1116 v6
du_'8729''45'cong'691'_1116 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_1116 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
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
-- Algebra.Lattice.Structures._.IsIdempotentCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_1118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_1118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_1118 v6
du_'8729''45'cong'737'_1118 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_1118 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
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
-- Algebra.Lattice.Structures.IsSemilattice
d_IsSemilattice_2766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_IsSemilattice_2766 = erased
-- Algebra.Lattice.Structures.IsSemilattice._.comm
d_comm_2776 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_2776 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_622 (coe v0)
-- Algebra.Lattice.Structures.IsSemilattice._.isBand
d_isBand_2778 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_2778 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Algebra.Lattice.Structures.IsSemilattice._.assoc
d_assoc_2782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2782 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_assoc_2782 v5
du_assoc_2782 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_2782 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Algebra.Lattice.Structures.IsSemilattice._.idem
d_idem_2784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
d_idem_2784 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_idem_2784 v5
du_idem_2784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
du_idem_2784 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_idem_536
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Algebra.Lattice.Structures.IsSemilattice._.isEquivalence
d_isEquivalence_2786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2786 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_2786 v5
du_isEquivalence_2786 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2786 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Algebra.Lattice.Structures.IsSemilattice._.isMagma
d_isMagma_2788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2788 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_2788 v5
du_isMagma_2788 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2788 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Algebra.Lattice.Structures.IsSemilattice._.isPartialEquivalence
d_isPartialEquivalence_2790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2790 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_2790 v5
du_isPartialEquivalence_2790 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2790 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Algebra.Lattice.Structures.IsSemilattice._.isSemigroup
d_isSemigroup_2792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2792 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_2792 v5
du_isSemigroup_2792 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2792 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Algebra.Lattice.Structures.IsSemilattice._.refl
d_refl_2794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
d_refl_2794 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_2794 v5
du_refl_2794 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
du_refl_2794 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsSemilattice._.reflexive
d_reflexive_2796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2796 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_2796 v5
du_reflexive_2796 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2796 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3))
                 v4)))
-- Algebra.Lattice.Structures.IsSemilattice._.setoid
d_setoid_2798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2798 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_2798 v5
du_setoid_2798 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2798 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Algebra.Lattice.Structures.IsSemilattice._.sym
d_sym_2800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2800 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_sym_2800 v5
du_sym_2800 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2800 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsSemilattice._.trans
d_trans_2802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2802 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_trans_2802 v5
du_trans_2802 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2802 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsSemilattice._.∙-cong
d_'8729''45'cong_2804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2804 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong_2804 v5
du_'8729''45'cong_2804 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_2804 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Algebra.Lattice.Structures.IsSemilattice._.∙-congʳ
d_'8729''45'cong'691'_2806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2806 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_2806 v5
du_'8729''45'cong'691'_2806 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2806 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
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
-- Algebra.Lattice.Structures.IsSemilattice._.∙-congˡ
d_'8729''45'cong'737'_2808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2808 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_2808 v5
du_'8729''45'cong'737'_2808 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2808 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
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
-- Algebra.Lattice.Structures.IsMeetSemilattice
d_IsMeetSemilattice_2810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_IsMeetSemilattice_2810 = erased
-- Algebra.Lattice.Structures.IsMeetSemilattice._.assoc
d_assoc_2820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2820 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_assoc_2820 v5
du_assoc_2820 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_2820 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.comm
d_comm_2822 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_2822 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_622 (coe v0)
-- Algebra.Lattice.Structures.IsMeetSemilattice._.idem
d_idem_2824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
d_idem_2824 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_idem_2824 v5
du_idem_2824 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
du_idem_2824 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_idem_536
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.isBand
d_isBand_2826 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_2826 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Algebra.Lattice.Structures.IsMeetSemilattice._.isEquivalence
d_isEquivalence_2828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2828 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_2828 v5
du_isEquivalence_2828 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2828 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.isMagma
d_isMagma_2830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2830 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_2830 v5
du_isMagma_2830 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2830 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.isPartialEquivalence
d_isPartialEquivalence_2832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2832 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_2832 v5
du_isPartialEquivalence_2832 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2832 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.isSemigroup
d_isSemigroup_2834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2834 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_2834 v5
du_isSemigroup_2834 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2834 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.refl
d_refl_2836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
d_refl_2836 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_2836 v5
du_refl_2836 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
du_refl_2836 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.reflexive
d_reflexive_2838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2838 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_2838 v5
du_reflexive_2838 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2838 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3))
                 v4)))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.setoid
d_setoid_2840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2840 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_2840 v5
du_setoid_2840 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2840 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.sym
d_sym_2842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2842 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_sym_2842 v5
du_sym_2842 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2842 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.trans
d_trans_2844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2844 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_trans_2844 v5
du_trans_2844 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2844 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.∙-cong
d_'8729''45'cong_2846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2846 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong_2846 v5
du_'8729''45'cong_2846 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_2846 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Algebra.Lattice.Structures.IsMeetSemilattice._.∙-congʳ
d_'8729''45'cong'691'_2848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2848 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_2848 v5
du_'8729''45'cong'691'_2848 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2848 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
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
-- Algebra.Lattice.Structures.IsMeetSemilattice._.∙-congˡ
d_'8729''45'cong'737'_2850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2850 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_2850 v5
du_'8729''45'cong'737'_2850 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2850 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
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
-- Algebra.Lattice.Structures.IsJoinSemilattice
d_IsJoinSemilattice_2852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_IsJoinSemilattice_2852 = erased
-- Algebra.Lattice.Structures.IsJoinSemilattice._.assoc
d_assoc_2862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2862 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_assoc_2862 v5
du_assoc_2862 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_2862 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.comm
d_comm_2864 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_2864 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_622 (coe v0)
-- Algebra.Lattice.Structures.IsJoinSemilattice._.idem
d_idem_2866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
d_idem_2866 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_idem_2866 v5
du_idem_2866 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
du_idem_2866 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_idem_536
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.isBand
d_isBand_2868 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_2868 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Algebra.Lattice.Structures.IsJoinSemilattice._.isEquivalence
d_isEquivalence_2870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2870 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_2870 v5
du_isEquivalence_2870 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2870 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.isMagma
d_isMagma_2872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2872 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_2872 v5
du_isMagma_2872 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2872 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.isPartialEquivalence
d_isPartialEquivalence_2874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2874 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_2874 v5
du_isPartialEquivalence_2874 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2874 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.isSemigroup
d_isSemigroup_2876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2876 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_2876 v5
du_isSemigroup_2876 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2876 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.refl
d_refl_2878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
d_refl_2878 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_2878 v5
du_refl_2878 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny
du_refl_2878 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.reflexive
d_reflexive_2880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2880 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_2880 v5
du_reflexive_2880 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2880 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3))
                 v4)))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.setoid
d_setoid_2882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2882 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_2882 v5
du_setoid_2882 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2882 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.sym
d_sym_2884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2884 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_sym_2884 v5
du_sym_2884 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2884 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.trans
d_trans_2886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2886 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_trans_2886 v5
du_trans_2886 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2886 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.∙-cong
d_'8729''45'cong_2888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2888 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong_2888 v5
du_'8729''45'cong_2888 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_2888 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Algebra.Lattice.Structures.IsJoinSemilattice._.∙-congʳ
d_'8729''45'cong'691'_2890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2890 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_2890 v5
du_'8729''45'cong'691'_2890 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2890 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
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
-- Algebra.Lattice.Structures.IsJoinSemilattice._.∙-congˡ
d_'8729''45'cong'737'_2892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2892 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_2892 v5
du_'8729''45'cong'737'_2892 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2892 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
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
-- Algebra.Lattice.Structures.IsBoundedSemilattice
d_IsBoundedSemilattice_2894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_IsBoundedSemilattice_2894 = erased
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.assoc
d_assoc_2906 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2906 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
               (coe v0))))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.comm
d_comm_2908 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_2908 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_776
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.idem
d_idem_2910 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_idem_2910 v0
  = coe MAlonzo.Code.Algebra.Structures.d_idem_896 (coe v0)
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.identity
d_identity_2912 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2912 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.identityʳ
d_identity'691'_2914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_identity'691'_2914 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_2914 v6
du_identity'691'_2914 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_identity'691'_2914 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_754
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.identityˡ
d_identity'737'_2916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_identity'737'_2916 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_2916 v6
du_identity'737'_2916 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_identity'737'_2916 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'737'_752
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isBand
d_isBand_2918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_2918 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isBand_2918 v6
du_isBand_2918 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_2918 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isCommutativeMagma
d_isCommutativeMagma_2920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2920 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeMagma_2920 v6
du_isCommutativeMagma_2920 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2920 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isCommutativeMonoid
d_isCommutativeMonoid_2922 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2922 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0)
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isCommutativeSemigroup
d_isCommutativeSemigroup_2924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeSemigroup_2924 v6
du_isCommutativeSemigroup_2924 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2924 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isEquivalence
d_isEquivalence_2926 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2926 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                  (coe v0)))))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isIdempotentMonoid
d_isIdempotentMonoid_2928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_2928 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isIdempotentMonoid_2928 v6
du_isIdempotentMonoid_2928 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_2928 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0)
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isMagma
d_isMagma_2930 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2930 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
               (coe v0))))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isMonoid
d_isMonoid_2932 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2932 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isPartialEquivalence
d_isPartialEquivalence_2934 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2934 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_2934 v6
du_isPartialEquivalence_2934 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2934 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
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
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isSemigroup
d_isSemigroup_2936 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2936 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isCommutativeBand
d_isCommutativeBand_2938 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_2938 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeBand_2938 v6
du_isCommutativeBand_2938 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_2938 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v0)
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.isUnitalMagma
d_isUnitalMagma_2940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isUnitalMagma_2940 v6
du_isUnitalMagma_2940 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2940 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.refl
d_refl_2942 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_refl_2942 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                     (coe v0))))))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.reflexive
d_reflexive_2944 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2944 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_2944 v6
du_reflexive_2944 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2944 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
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
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.setoid
d_setoid_2946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_2946 v6
du_setoid_2946 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2946 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.sym
d_sym_2948 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2948 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                     (coe v0))))))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.trans
d_trans_2950 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2950 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                     (coe v0))))))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.∙-cong
d_'8729''45'cong_2952 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_2952 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                  (coe v0)))))
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.∙-congʳ
d_'8729''45'cong'691'_2954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_2954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_2954 v6
du_'8729''45'cong'691'_2954 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_2954 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
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
-- Algebra.Lattice.Structures.IsBoundedSemilattice._.∙-congˡ
d_'8729''45'cong'737'_2956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_2956 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_2956 v6
du_'8729''45'cong'737'_2956 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_2956 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1) in
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
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice
d_IsBoundedMeetSemilattice_2958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_IsBoundedMeetSemilattice_2958 = erased
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.identity
d_identity_2970 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2970 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.identityʳ
d_identity'691'_2972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_identity'691'_2972 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_2972 v6
du_identity'691'_2972 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_identity'691'_2972 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_754
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.identityˡ
d_identity'737'_2974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_identity'737'_2974 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_2974 v6
du_identity'737'_2974 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_identity'737'_2974 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'737'_752
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.isCommutativeBand
d_isCommutativeBand_2976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_2976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeBand_2976 v6
du_isCommutativeBand_2976 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_2976 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v0)
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.assoc
d_assoc_2980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_assoc_2980 v6
du_assoc_2980 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_2980 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.comm
d_comm_2982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_2982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_comm_2982 v6
du_comm_2982 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_comm_2982 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_776
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.idem
d_idem_2984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_idem_2984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_idem_2984 v6
du_idem_2984 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_idem_2984 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_536
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.isBand
d_isBand_2986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_2986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isBand_2986 v6
du_isBand_2986 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_2986 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.isEquivalence
d_isEquivalence_2988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_2988 v6
du_isEquivalence_2988 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2988 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.isMagma
d_isMagma_2990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isMagma_2990 v6
du_isMagma_2990 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2990 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.isPartialEquivalence
d_isPartialEquivalence_2992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2992 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_2992 v6
du_isPartialEquivalence_2992 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2992 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.isSemigroup
d_isSemigroup_2994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2994 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isSemigroup_2994 v6
du_isSemigroup_2994 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2994 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.refl
d_refl_2996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_refl_2996 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_2996 v6
du_refl_2996 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_refl_2996 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.reflexive
d_reflexive_2998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2998 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_2998 v6
du_reflexive_2998 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2998 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))
                    v5))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.setoid
d_setoid_3000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3000 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_3000 v6
du_setoid_3000 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3000 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.sym
d_sym_3002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_3002 v6
du_sym_3002 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_3002 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.trans
d_trans_3004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3004 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_3004 v6
du_trans_3004 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_3004 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.∙-cong
d_'8729''45'cong_3006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3006 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong_3006 v6
du_'8729''45'cong_3006 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_3006 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.∙-congʳ
d_'8729''45'cong'691'_3008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3008 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_3008 v6
du_'8729''45'cong'691'_3008 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3008 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
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
-- Algebra.Lattice.Structures.IsBoundedMeetSemilattice._.∙-congˡ
d_'8729''45'cong'737'_3010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3010 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_3010 v6
du_'8729''45'cong'737'_3010 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3010 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
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
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice
d_IsBoundedJoinSemilattice_3012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_IsBoundedJoinSemilattice_3012 = erased
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.identity
d_identity_3024 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_3024 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.identityʳ
d_identity'691'_3026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_identity'691'_3026 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'691'_3026 v6
du_identity'691'_3026 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_identity'691'_3026 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_754
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.identityˡ
d_identity'737'_3028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_identity'737'_3028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_identity'737'_3028 v6
du_identity'737'_3028 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_identity'737'_3028 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'737'_752
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.isCommutativeBand
d_isCommutativeBand_3030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_3030 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isCommutativeBand_3030 v6
du_isCommutativeBand_3030 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_3030 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v0)
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.assoc
d_assoc_3034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_3034 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_assoc_3034 v6
du_assoc_3034 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_3034 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.comm
d_comm_3036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_3036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_comm_3036 v6
du_comm_3036 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_comm_3036 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_776
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.idem
d_idem_3038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_idem_3038 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_idem_3038 v6
du_idem_3038 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_idem_3038 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_536
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.isBand
d_isBand_3040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_3040 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isBand_3040 v6
du_isBand_3040 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_3040 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.isEquivalence
d_isEquivalence_3042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3042 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_3042 v6
du_isEquivalence_3042 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_3042 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.isMagma
d_isMagma_3044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_3044 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isMagma_3044 v6
du_isMagma_3044 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_3044 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.isPartialEquivalence
d_isPartialEquivalence_3046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3046 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_3046 v6
du_isPartialEquivalence_3046 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3046 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.isSemigroup
d_isSemigroup_3048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_3048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isSemigroup_3048 v6
du_isSemigroup_3048 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_3048 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.refl
d_refl_3050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
d_refl_3050 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_3050 v6
du_refl_3050 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny
du_refl_3050 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.reflexive
d_reflexive_3052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3052 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_3052 v6
du_reflexive_3052 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3052 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))
                    v5))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.setoid
d_setoid_3054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3054 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_3054 v6
du_setoid_3054 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3054 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.sym
d_sym_3056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3056 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_3056 v6
du_sym_3056 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_3056 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.trans
d_trans_3058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3058 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_3058 v6
du_trans_3058 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_3058 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.∙-cong
d_'8729''45'cong_3060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_3060 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong_3060 v6
du_'8729''45'cong_3060 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_3060 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.∙-congʳ
d_'8729''45'cong'691'_3062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_3062 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_3062 v6
du_'8729''45'cong'691'_3062 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_3062 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
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
-- Algebra.Lattice.Structures.IsBoundedJoinSemilattice._.∙-congˡ
d_'8729''45'cong'737'_3064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_3064 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_3064 v6
du_'8729''45'cong'737'_3064 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_3064 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
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
-- Algebra.Lattice.Structures.IsLattice
d_IsLattice_3070 a0 a1 a2 a3 a4 a5 = ()
data T_IsLattice_3070
  = C_constructor_3140 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
                       (AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny ->
                        AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Lattice.Structures.IsLattice.isEquivalence
d_isEquivalence_3092 ::
  T_IsLattice_3070 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3092 v0
  = case coe v0 of
      C_constructor_3140 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsLattice.∨-comm
d_'8744''45'comm_3094 ::
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_3094 v0
  = case coe v0 of
      C_constructor_3140 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsLattice.∨-assoc
d_'8744''45'assoc_3096 ::
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_3096 v0
  = case coe v0 of
      C_constructor_3140 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsLattice.∨-cong
d_'8744''45'cong_3098 ::
  T_IsLattice_3070 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_3098 v0
  = case coe v0 of
      C_constructor_3140 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsLattice.∧-comm
d_'8743''45'comm_3100 ::
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_3100 v0
  = case coe v0 of
      C_constructor_3140 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsLattice.∧-assoc
d_'8743''45'assoc_3102 ::
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_3102 v0
  = case coe v0 of
      C_constructor_3140 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsLattice.∧-cong
d_'8743''45'cong_3104 ::
  T_IsLattice_3070 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_3104 v0
  = case coe v0 of
      C_constructor_3140 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsLattice.absorptive
d_absorptive_3106 ::
  T_IsLattice_3070 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_3106 v0
  = case coe v0 of
      C_constructor_3140 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsLattice._.isPartialEquivalence
d_isPartialEquivalence_3110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_3070 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_3110 v6
du_isPartialEquivalence_3110 ::
  T_IsLattice_3070 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3110 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe d_isEquivalence_3092 (coe v0))
-- Algebra.Lattice.Structures.IsLattice._.refl
d_refl_3112 :: T_IsLattice_3070 -> AgdaAny -> AgdaAny
d_refl_3112 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_3092 (coe v0))
-- Algebra.Lattice.Structures.IsLattice._.reflexive
d_reflexive_3114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_3070 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_3114 v6
du_reflexive_3114 ::
  T_IsLattice_3070 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
      (coe d_isEquivalence_3092 (coe v0)) v1
-- Algebra.Lattice.Structures.IsLattice._.sym
d_sym_3116 ::
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3116 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_3092 (coe v0))
-- Algebra.Lattice.Structures.IsLattice._.trans
d_trans_3118 ::
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3118 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_3092 (coe v0))
-- Algebra.Lattice.Structures.IsLattice.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_3120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_3120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'absorbs'45''8743'_3120 v6
du_'8744''45'absorbs'45''8743'_3120 ::
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_3120 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_absorptive_3106 (coe v0))
-- Algebra.Lattice.Structures.IsLattice.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_3122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_3122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'absorbs'45''8744'_3122 v6
du_'8743''45'absorbs'45''8744'_3122 ::
  T_IsLattice_3070 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_3122 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_absorptive_3106 (coe v0))
-- Algebra.Lattice.Structures.IsLattice.∧-congˡ
d_'8743''45'cong'737'_3124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_3124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_'8743''45'cong'737'_3124 v6 v7 v8 v9 v10
du_'8743''45'cong'737'_3124 ::
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_3124 v0 v1 v2 v3 v4
  = coe
      d_'8743''45'cong_3104 v0 v1 v1 v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (d_isEquivalence_3092 (coe v0)) v1)
      v4
-- Algebra.Lattice.Structures.IsLattice.∧-congʳ
d_'8743''45'cong'691'_3128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_3128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_'8743''45'cong'691'_3128 v6 v7 v8 v9 v10
du_'8743''45'cong'691'_3128 ::
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_3128 v0 v1 v2 v3 v4
  = coe
      d_'8743''45'cong_3104 v0 v2 v3 v1 v1 v4
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (d_isEquivalence_3092 (coe v0)) v1)
-- Algebra.Lattice.Structures.IsLattice.∨-congˡ
d_'8744''45'cong'737'_3132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_3132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_'8744''45'cong'737'_3132 v6 v7 v8 v9 v10
du_'8744''45'cong'737'_3132 ::
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_3132 v0 v1 v2 v3 v4
  = coe
      d_'8744''45'cong_3098 v0 v1 v1 v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (d_isEquivalence_3092 (coe v0)) v1)
      v4
-- Algebra.Lattice.Structures.IsLattice.∨-congʳ
d_'8744''45'cong'691'_3136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_3136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_'8744''45'cong'691'_3136 v6 v7 v8 v9 v10
du_'8744''45'cong'691'_3136 ::
  T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_3136 v0 v1 v2 v3 v4
  = coe
      d_'8744''45'cong_3098 v0 v2 v3 v1 v1 v4
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (d_isEquivalence_3092 (coe v0)) v1)
-- Algebra.Lattice.Structures.IsDistributiveLattice
d_IsDistributiveLattice_3146 a0 a1 a2 a3 a4 a5 = ()
data T_IsDistributiveLattice_3146
  = C_constructor_3212 T_IsLattice_3070
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Lattice.Structures.IsDistributiveLattice.isLattice
d_isLattice_3158 ::
  T_IsDistributiveLattice_3146 -> T_IsLattice_3070
d_isLattice_3158 v0
  = case coe v0 of
      C_constructor_3212 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsDistributiveLattice.∨-distrib-∧
d_'8744''45'distrib'45''8743'_3160 ::
  T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_3160 v0
  = case coe v0 of
      C_constructor_3212 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsDistributiveLattice.∧-distrib-∨
d_'8743''45'distrib'45''8744'_3162 ::
  T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_3162 v0
  = case coe v0 of
      C_constructor_3212 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsDistributiveLattice._.absorptive
d_absorptive_3166 ::
  T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_3166 v0
  = coe d_absorptive_3106 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.isEquivalence
d_isEquivalence_3168 ::
  T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3168 v0
  = coe d_isEquivalence_3092 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.isPartialEquivalence
d_isPartialEquivalence_3170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_3170 v6
du_isPartialEquivalence_3170 ::
  T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3170 v0
  = let v1 = d_isLattice_3158 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe d_isEquivalence_3092 (coe v1)))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.refl
d_refl_3172 :: T_IsDistributiveLattice_3146 -> AgdaAny -> AgdaAny
d_refl_3172 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe d_isEquivalence_3092 (coe d_isLattice_3158 (coe v0)))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.reflexive
d_reflexive_3174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_3174 v6
du_reflexive_3174 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3174 v0
  = let v1 = d_isLattice_3158 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe d_isEquivalence_3092 (coe v1)) v2)
-- Algebra.Lattice.Structures.IsDistributiveLattice._.sym
d_sym_3176 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe d_isEquivalence_3092 (coe d_isLattice_3158 (coe v0)))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.trans
d_trans_3178 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe d_isEquivalence_3092 (coe d_isLattice_3158 (coe v0)))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_3180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_3180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'absorbs'45''8744'_3180 v6
du_'8743''45'absorbs'45''8744'_3180 ::
  T_IsDistributiveLattice_3146 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_3180 v0
  = coe
      du_'8743''45'absorbs'45''8744'_3122 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∧-assoc
d_'8743''45'assoc_3182 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_3182 v0
  = coe d_'8743''45'assoc_3102 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∧-comm
d_'8743''45'comm_3184 ::
  T_IsDistributiveLattice_3146 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_3184 v0
  = coe d_'8743''45'comm_3100 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∧-cong
d_'8743''45'cong_3186 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_3186 v0
  = coe d_'8743''45'cong_3104 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∧-congʳ
d_'8743''45'cong'691'_3188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_3188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'cong'691'_3188 v6
du_'8743''45'cong'691'_3188 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_3188 v0
  = coe du_'8743''45'cong'691'_3128 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∧-congˡ
d_'8743''45'cong'737'_3190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_3190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'cong'737'_3190 v6
du_'8743''45'cong'737'_3190 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_3190 v0
  = coe du_'8743''45'cong'737'_3124 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_3192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_3192 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'absorbs'45''8743'_3192 v6
du_'8744''45'absorbs'45''8743'_3192 ::
  T_IsDistributiveLattice_3146 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_3192 v0
  = coe
      du_'8744''45'absorbs'45''8743'_3120 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∨-assoc
d_'8744''45'assoc_3194 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_3194 v0
  = coe d_'8744''45'assoc_3096 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∨-comm
d_'8744''45'comm_3196 ::
  T_IsDistributiveLattice_3146 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_3196 v0
  = coe d_'8744''45'comm_3094 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∨-cong
d_'8744''45'cong_3198 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_3198 v0
  = coe d_'8744''45'cong_3098 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∨-congʳ
d_'8744''45'cong'691'_3200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_3200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'cong'691'_3200 v6
du_'8744''45'cong'691'_3200 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_3200 v0
  = coe du_'8744''45'cong'691'_3136 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice._.∨-congˡ
d_'8744''45'cong'737'_3202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_3202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'cong'737'_3202 v6
du_'8744''45'cong'737'_3202 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_3202 v0
  = coe du_'8744''45'cong'737'_3132 (coe d_isLattice_3158 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_3204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_3204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'distrib'737''45''8743'_3204 v6
du_'8744''45'distrib'737''45''8743'_3204 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_3204 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'8744''45'distrib'45''8743'_3160 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_3206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_3206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'distrib'691''45''8743'_3206 v6
du_'8744''45'distrib'691''45''8743'_3206 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_3206 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'8744''45'distrib'45''8743'_3160 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_3208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_3208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'distrib'737''45''8744'_3208 v6
du_'8743''45'distrib'737''45''8744'_3208 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_3208 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'8743''45'distrib'45''8744'_3162 (coe v0))
-- Algebra.Lattice.Structures.IsDistributiveLattice.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_3210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_3210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'distrib'691''45''8744'_3210 v6
du_'8743''45'distrib'691''45''8744'_3210 ::
  T_IsDistributiveLattice_3146 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_3210 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'8743''45'distrib'45''8744'_3162 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra
d_IsBooleanAlgebra_3224 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsBooleanAlgebra_3224
  = C_constructor_3314 T_IsDistributiveLattice_3146
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Lattice.Structures.IsBooleanAlgebra.isDistributiveLattice
d_isDistributiveLattice_3244 ::
  T_IsBooleanAlgebra_3224 -> T_IsDistributiveLattice_3146
d_isDistributiveLattice_3244 v0
  = case coe v0 of
      C_constructor_3314 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsBooleanAlgebra.∨-complement
d_'8744''45'complement_3246 ::
  T_IsBooleanAlgebra_3224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_3246 v0
  = case coe v0 of
      C_constructor_3314 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsBooleanAlgebra.∧-complement
d_'8743''45'complement_3248 ::
  T_IsBooleanAlgebra_3224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_3248 v0
  = case coe v0 of
      C_constructor_3314 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsBooleanAlgebra.¬-cong
d_'172''45'cong_3250 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'cong_3250 v0
  = case coe v0 of
      C_constructor_3314 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.absorptive
d_absorptive_3254 ::
  T_IsBooleanAlgebra_3224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_3254 v0
  = coe
      d_absorptive_3106
      (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.isEquivalence
d_isEquivalence_3256 ::
  T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3256 v0
  = coe
      d_isEquivalence_3092
      (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.isLattice
d_isLattice_3258 :: T_IsBooleanAlgebra_3224 -> T_IsLattice_3070
d_isLattice_3258 v0
  = coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.isPartialEquivalence
d_isPartialEquivalence_3260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_3260 v9
du_isPartialEquivalence_3260 ::
  T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3260 v0
  = let v1 = d_isDistributiveLattice_3244 (coe v0) in
    coe
      (let v2 = d_isLattice_3158 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe d_isEquivalence_3092 (coe v2))))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.refl
d_refl_3262 :: T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
d_refl_3262 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         d_isEquivalence_3092
         (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0))))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.reflexive
d_reflexive_3264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_3264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_3264 v9
du_reflexive_3264 ::
  T_IsBooleanAlgebra_3224 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_3264 v0
  = let v1 = d_isDistributiveLattice_3244 (coe v0) in
    coe
      (let v2 = d_isLattice_3158 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe d_isEquivalence_3092 (coe v2)) v3))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.sym
d_sym_3266 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_3266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         d_isEquivalence_3092
         (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0))))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.trans
d_trans_3268 ::
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_3268 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         d_isEquivalence_3092
         (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0))))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_3270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_3270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 v9
  = du_'8743''45'absorbs'45''8744'_3270 v9
du_'8743''45'absorbs'45''8744'_3270 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_3270 v0
  = let v1 = d_isDistributiveLattice_3244 (coe v0) in
    coe
      (coe
         du_'8743''45'absorbs'45''8744'_3122
         (coe d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-assoc
d_'8743''45'assoc_3272 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_3272 v0
  = coe
      d_'8743''45'assoc_3102
      (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-comm
d_'8743''45'comm_3274 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_3274 v0
  = coe
      d_'8743''45'comm_3100
      (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-cong
d_'8743''45'cong_3276 ::
  T_IsBooleanAlgebra_3224 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_3276 v0
  = coe
      d_'8743''45'cong_3104
      (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-congʳ
d_'8743''45'cong'691'_3278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_3278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8743''45'cong'691'_3278 v9
du_'8743''45'cong'691'_3278 ::
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_3278 v0
  = let v1 = d_isDistributiveLattice_3244 (coe v0) in
    coe
      (coe du_'8743''45'cong'691'_3128 (coe d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-congˡ
d_'8743''45'cong'737'_3280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_3280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8743''45'cong'737'_3280 v9
du_'8743''45'cong'737'_3280 ::
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_3280 v0
  = let v1 = d_isDistributiveLattice_3244 (coe v0) in
    coe
      (coe du_'8743''45'cong'737'_3124 (coe d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-distrib-∨
d_'8743''45'distrib'45''8744'_3282 ::
  T_IsBooleanAlgebra_3224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_3282 v0
  = coe
      d_'8743''45'distrib'45''8744'_3162
      (coe d_isDistributiveLattice_3244 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_3284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_3284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 v9
  = du_'8743''45'distrib'691''45''8744'_3284 v9
du_'8743''45'distrib'691''45''8744'_3284 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_3284 v0
  = coe
      du_'8743''45'distrib'691''45''8744'_3210
      (coe d_isDistributiveLattice_3244 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_3286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_3286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 v9
  = du_'8743''45'distrib'737''45''8744'_3286 v9
du_'8743''45'distrib'737''45''8744'_3286 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_3286 v0
  = coe
      du_'8743''45'distrib'737''45''8744'_3208
      (coe d_isDistributiveLattice_3244 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_3288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_3288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 v9
  = du_'8744''45'absorbs'45''8743'_3288 v9
du_'8744''45'absorbs'45''8743'_3288 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_3288 v0
  = let v1 = d_isDistributiveLattice_3244 (coe v0) in
    coe
      (coe
         du_'8744''45'absorbs'45''8743'_3120
         (coe d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-assoc
d_'8744''45'assoc_3290 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_3290 v0
  = coe
      d_'8744''45'assoc_3096
      (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-comm
d_'8744''45'comm_3292 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_3292 v0
  = coe
      d_'8744''45'comm_3094
      (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-cong
d_'8744''45'cong_3294 ::
  T_IsBooleanAlgebra_3224 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_3294 v0
  = coe
      d_'8744''45'cong_3098
      (coe d_isLattice_3158 (coe d_isDistributiveLattice_3244 (coe v0)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-congʳ
d_'8744''45'cong'691'_3296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_3296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8744''45'cong'691'_3296 v9
du_'8744''45'cong'691'_3296 ::
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_3296 v0
  = let v1 = d_isDistributiveLattice_3244 (coe v0) in
    coe
      (coe du_'8744''45'cong'691'_3136 (coe d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-congˡ
d_'8744''45'cong'737'_3298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_3298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8744''45'cong'737'_3298 v9
du_'8744''45'cong'737'_3298 ::
  T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_3298 v0
  = let v1 = d_isDistributiveLattice_3244 (coe v0) in
    coe
      (coe du_'8744''45'cong'737'_3132 (coe d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-distrib-∧
d_'8744''45'distrib'45''8743'_3300 ::
  T_IsBooleanAlgebra_3224 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_3300 v0
  = coe
      d_'8744''45'distrib'45''8743'_3160
      (coe d_isDistributiveLattice_3244 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_3302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_3302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 v9
  = du_'8744''45'distrib'691''45''8743'_3302 v9
du_'8744''45'distrib'691''45''8743'_3302 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_3302 v0
  = coe
      du_'8744''45'distrib'691''45''8743'_3206
      (coe d_isDistributiveLattice_3244 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra._.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_3304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_3304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 v9
  = du_'8744''45'distrib'737''45''8743'_3304 v9
du_'8744''45'distrib'737''45''8743'_3304 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_3304 v0
  = coe
      du_'8744''45'distrib'737''45''8743'_3204
      (coe d_isDistributiveLattice_3244 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra.∨-complementˡ
d_'8744''45'complement'737'_3306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
d_'8744''45'complement'737'_3306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 v9
  = du_'8744''45'complement'737'_3306 v9
du_'8744''45'complement'737'_3306 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
du_'8744''45'complement'737'_3306 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'8744''45'complement_3246 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra.∨-complementʳ
d_'8744''45'complement'691'_3308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
d_'8744''45'complement'691'_3308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 v9
  = du_'8744''45'complement'691'_3308 v9
du_'8744''45'complement'691'_3308 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
du_'8744''45'complement'691'_3308 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'8744''45'complement_3246 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra.∧-complementˡ
d_'8743''45'complement'737'_3310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
d_'8743''45'complement'737'_3310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 v9
  = du_'8743''45'complement'737'_3310 v9
du_'8743''45'complement'737'_3310 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
du_'8743''45'complement'737'_3310 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_'8743''45'complement_3248 (coe v0))
-- Algebra.Lattice.Structures.IsBooleanAlgebra.∧-complementʳ
d_'8743''45'complement'691'_3312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
d_'8743''45'complement'691'_3312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 v9
  = du_'8743''45'complement'691'_3312 v9
du_'8743''45'complement'691'_3312 ::
  T_IsBooleanAlgebra_3224 -> AgdaAny -> AgdaAny
du_'8743''45'complement'691'_3312 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_'8743''45'complement_3248 (coe v0))
