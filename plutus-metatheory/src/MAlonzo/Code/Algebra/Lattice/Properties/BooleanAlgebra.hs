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

module MAlonzo.Code.Algebra.Lattice.Properties.BooleanAlgebra where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Consequences.Setoid qualified
import MAlonzo.Code.Algebra.Lattice.Bundles qualified
import MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice qualified
import MAlonzo.Code.Algebra.Lattice.Properties.Lattice qualified
import MAlonzo.Code.Algebra.Lattice.Properties.Semilattice qualified
import MAlonzo.Code.Algebra.Lattice.Structures qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Lattice.Bundles qualified
import MAlonzo.Code.Relation.Binary.Lattice.Structures qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Single qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Lattice.Properties.BooleanAlgebra._.IsAbelianGroup
d_IsAbelianGroup_116 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeMonoid
d_IsCommutativeMonoid_128 a0 a1 a2 a3 a4 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeRing
d_IsCommutativeRing_130 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeSemiring
d_IsCommutativeSemiring_134 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsGroup
d_IsGroup_140 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMagma
d_IsMagma_160 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMonoid
d_IsMonoid_166 a0 a1 a2 a3 a4 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing
d_IsRing_182 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemigroup
d_IsSemigroup_188 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemiring
d_IsSemiring_192 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsAbelianGroup.comm
d_comm_208 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_208 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_1146 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsAbelianGroup.isGroup
d_isGroup_230 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_230 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeMonoid.comm
d_comm_498 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_498 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_748 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeMonoid.isMonoid
d_isMonoid_514 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_514 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeRing.*-comm
d_'42''45'comm_544 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_544 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'comm_2814 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeRing.isRing
d_isRing_632 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_isRing_632 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeSemiring.*-comm
d_'42''45'comm_698 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_698 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1694 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeSemiring.isSemiring
d_isSemiring_768 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_768 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsGroup.inverse
d_inverse_896 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_896 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1052 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsGroup.isMonoid
d_isMonoid_910 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_910 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_932 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_932 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1054 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMagma.isEquivalence
d_isEquivalence_1460 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1460 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMagma.∙-cong
d_'8729''45'cong_1474 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1474 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMonoid.identity
d_identity_1570 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1570 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_698 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMonoid.isSemigroup
d_isSemigroup_1582 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1582 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.*-assoc
d_'42''45'assoc_2088 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2088 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2676 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.*-cong
d_'42''45'cong_2090 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2090 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_2674 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.*-identity
d_'42''45'identity_2096 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2096 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2678 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2124 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2124 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.distrib
d_distrib_2154 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2154 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2680 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemigroup.assoc
d_assoc_2314 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2314 v0
  = coe MAlonzo.Code.Algebra.Structures.d_assoc_482 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemigroup.isMagma
d_isMagma_2318 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2318 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2432 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2432 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemiring.zero
d_zero_2446 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2446 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1586 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._._DistributesOver_
d__DistributesOver__2632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__2632 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._._DistributesOverʳ_
d__DistributesOver'691'__2634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__2634 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._._DistributesOverˡ_
d__DistributesOver'737'__2636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__2636 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Associative
d_Associative_2652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Associative_2652 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Commutative
d_Commutative_2656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_2656 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Congruent₂
d_Congruent'8322'_2660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_2660 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Identity
d_Identity_2672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identity_2672 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Inverse
d_Inverse_2676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Inverse_2676 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Involutive
d_Involutive_2680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny) -> ()
d_Involutive_2680 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.LeftIdentity
d_LeftIdentity_2698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftIdentity_2698 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.LeftInverse
d_LeftInverse_2700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftInverse_2700 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.LeftZero
d_LeftZero_2706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftZero_2706 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.RightIdentity
d_RightIdentity_2728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightIdentity_2728 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.RightInverse
d_RightInverse_2730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightInverse_2730 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.RightZero
d_RightZero_2736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightZero_2736 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Zero
d_Zero_2756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Zero_2756 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra
d_IsBooleanAlgebra_2892 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra.isDistributiveLattice
d_isDistributiveLattice_2914 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_isDistributiveLattice_2914 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra.¬-cong
d_'172''45'cong_2930 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'cong_2930 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra.∧-complement
d_'8743''45'complement_2938 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_2938 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3136
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra.∨-complement
d_'8744''45'complement_2962 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_2962 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3134
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.poset
d_poset_3356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_3356 ~v0 ~v1 v2 = du_poset_3356 v2
du_poset_3356 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_3356 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_poset_162
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-idem
d_'8743''45'idem_3358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8743''45'idem_3358 ~v0 ~v1 v2 = du_'8743''45'idem_3358 v2
du_'8743''45'idem_3358 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8743''45'idem_3358 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_3182
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isBand
d_'8743''45'isBand_3360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8743''45'isBand_3360 ~v0 ~v1 v2 = du_'8743''45'isBand_3360 v2
du_'8743''45'isBand_3360 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8743''45'isBand_3360 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isBand_3190
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isMagma
d_'8743''45'isMagma_3362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8743''45'isMagma_3362 ~v0 ~v1 v2 = du_'8743''45'isMagma_3362 v2
du_'8743''45'isMagma_3362 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8743''45'isMagma_3362 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isMagma_3186
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_3364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_3364 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_3364 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_3364 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_3364 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_3366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_'8743''45'isOrderTheoreticMeetSemilattice_3366 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_3366 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_3366 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_'8743''45'isOrderTheoreticMeetSemilattice_3366 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isSemigroup
d_'8743''45'isSemigroup_3368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8743''45'isSemigroup_3368 ~v0 ~v1 v2
  = du_'8743''45'isSemigroup_3368 v2
du_'8743''45'isSemigroup_3368 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8743''45'isSemigroup_3368 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isSemigroup_3188
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isSemilattice
d_'8743''45'isSemilattice_3370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8743''45'isSemilattice_3370 ~v0 ~v1 v2
  = du_'8743''45'isSemilattice_3370 v2
du_'8743''45'isSemilattice_3370 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_'8743''45'isSemilattice_3370 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isSemilattice_3192
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_3372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_3372 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_3372 v2
du_'8743''45'orderTheoreticJoinSemilattice_3372 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_3372 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_3374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
d_'8743''45'orderTheoreticMeetSemilattice_3374 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_3374 v2
du_'8743''45'orderTheoreticMeetSemilattice_3374 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
du_'8743''45'orderTheoreticMeetSemilattice_3374 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-semilattice
d_'8743''45'semilattice_3376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8743''45'semilattice_3376 ~v0 ~v1 v2
  = du_'8743''45'semilattice_3376 v2
du_'8743''45'semilattice_3376 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8743''45'semilattice_3376 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-∨-distributiveLattice
d_'8743''45''8744''45'distributiveLattice_3378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8743''45''8744''45'distributiveLattice_3378 ~v0 ~v1 v2
  = du_'8743''45''8744''45'distributiveLattice_3378 v2
du_'8743''45''8744''45'distributiveLattice_3378 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
du_'8743''45''8744''45'distributiveLattice_3378 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice.du_'8743''45''8744''45'distributiveLattice_738
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
         (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-∨-isDistributiveLattice
d_'8743''45''8744''45'isDistributiveLattice_3380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_'8743''45''8744''45'isDistributiveLattice_3380 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isDistributiveLattice_3380 v2
du_'8743''45''8744''45'isDistributiveLattice_3380 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
du_'8743''45''8744''45'isDistributiveLattice_3380 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice.du_'8743''45''8744''45'isDistributiveLattice_736
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
         (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-∨-isLattice
d_'8743''45''8744''45'isLattice_3382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_'8743''45''8744''45'isLattice_3382 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isLattice_3382 v2
du_'8743''45''8744''45'isLattice_3382 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
du_'8743''45''8744''45'isLattice_3382 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45''8744''45'isLattice_3230
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-∨-lattice
d_'8743''45''8744''45'lattice_3384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8743''45''8744''45'lattice_3384 ~v0 ~v1 v2
  = du_'8743''45''8744''45'lattice_3384 v2
du_'8743''45''8744''45'lattice_3384 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
du_'8743''45''8744''45'lattice_3384 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45''8744''45'lattice_3232
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-idem
d_'8744''45'idem_3386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8744''45'idem_3386 ~v0 ~v1 v2 = du_'8744''45'idem_3386 v2
du_'8744''45'idem_3386 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8744''45'idem_3386 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'idem_3206
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-isBand
d_'8744''45'isBand_3388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8744''45'isBand_3388 ~v0 ~v1 v2 = du_'8744''45'isBand_3388 v2
du_'8744''45'isBand_3388 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8744''45'isBand_3388 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isBand_3214
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-isMagma
d_'8744''45'isMagma_3390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8744''45'isMagma_3390 ~v0 ~v1 v2 = du_'8744''45'isMagma_3390 v2
du_'8744''45'isMagma_3390 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8744''45'isMagma_3390 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isMagma_3210
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_3392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_3392 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_3392 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_3392 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_3392 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_3394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_'8743''45'isOrderTheoreticMeetSemilattice_3394 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_3394 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_3394 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_'8743''45'isOrderTheoreticMeetSemilattice_3394 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-isSemigroup
d_'8744''45'isSemigroup_3396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8744''45'isSemigroup_3396 ~v0 ~v1 v2
  = du_'8744''45'isSemigroup_3396 v2
du_'8744''45'isSemigroup_3396 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8744''45'isSemigroup_3396 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isSemigroup_3212
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-isSemilattice
d_'8744''45'isSemilattice_3398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8744''45'isSemilattice_3398 ~v0 ~v1 v2
  = du_'8744''45'isSemilattice_3398 v2
du_'8744''45'isSemilattice_3398 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_'8744''45'isSemilattice_3398 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isSemilattice_3216
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_3400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_3400 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_3400 v2
du_'8743''45'orderTheoreticJoinSemilattice_3400 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_3400 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_3402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
d_'8743''45'orderTheoreticMeetSemilattice_3402 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_3402 v2
du_'8743''45'orderTheoreticMeetSemilattice_3402 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
du_'8743''45'orderTheoreticMeetSemilattice_3402 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-semilattice
d_'8744''45'semilattice_3404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8744''45'semilattice_3404 ~v0 ~v1 v2
  = du_'8744''45'semilattice_3404 v2
du_'8744''45'semilattice_3404 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8744''45'semilattice_3404 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-∧-isOrderTheoreticLattice
d_'8744''45''8743''45'isOrderTheoreticLattice_3406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
d_'8744''45''8743''45'isOrderTheoreticLattice_3406 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isOrderTheoreticLattice_3406 v2
du_'8744''45''8743''45'isOrderTheoreticLattice_3406 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
du_'8744''45''8743''45'isOrderTheoreticLattice_3406 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45''8743''45'isOrderTheoreticLattice_3244
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-∧-orderTheoreticLattice
d_'8744''45''8743''45'orderTheoreticLattice_3408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_386
d_'8744''45''8743''45'orderTheoreticLattice_3408 ~v0 ~v1 v2
  = du_'8744''45''8743''45'orderTheoreticLattice_3408 v2
du_'8744''45''8743''45'orderTheoreticLattice_3408 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_386
du_'8744''45''8743''45'orderTheoreticLattice_3408 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45''8743''45'orderTheoreticLattice_3300
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-isBooleanAlgebra
d_'8743''45''8744''45'isBooleanAlgebra_3410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112
d_'8743''45''8744''45'isBooleanAlgebra_3410 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isBooleanAlgebra_3410 v2
du_'8743''45''8744''45'isBooleanAlgebra_3410 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112
du_'8743''45''8744''45'isBooleanAlgebra_3410 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsBooleanAlgebra'46'constructor_44015
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice.du_'8743''45''8744''45'isDistributiveLattice_736
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3136
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3134
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0)))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-booleanAlgebra
d_'8743''45''8744''45'booleanAlgebra_3412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682
d_'8743''45''8744''45'booleanAlgebra_3412 ~v0 ~v1 v2
  = du_'8743''45''8744''45'booleanAlgebra_3412 v2
du_'8743''45''8744''45'booleanAlgebra_3412 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682
du_'8743''45''8744''45'booleanAlgebra_3412 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_BooleanAlgebra'46'constructor_11509
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe du_'8743''45''8744''45'isBooleanAlgebra_3410 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-identityʳ
d_'8743''45'identity'691'_3414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8743''45'identity'691'_3414 ~v0 ~v1 v2 v3
  = du_'8743''45'identity'691'_3414 v2 v3
du_'8743''45'identity'691'_3414 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8743''45'identity'691'_3414 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v2
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
            v1 v1
            (let v2
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v2
                                 = coe
                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                     (coe v0) in
                           coe
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                   (coe v2))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v2))
                  (coe v1)))
            (let v2
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (let v3
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe v2) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3014
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                     v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))))
         (let v2
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (let v3
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                  (coe v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0)))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3196
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))
                        v1))))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-identityˡ
d_'8743''45'identity'737'_3418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8743''45'identity'737'_3418 ~v0 ~v1 v2
  = du_'8743''45'identity'737'_3418 v2
du_'8743''45'identity'737'_3418 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8743''45'identity'737'_3418 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'id'691''8658'id'737'_346
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe du_'8743''45'identity'691'_3414 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-identity
d_'8743''45'identity_3420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'identity_3420 ~v0 ~v1 v2
  = du_'8743''45'identity_3420 v2
du_'8743''45'identity_3420 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'identity_3420 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8743''45'identity'737'_3418 (coe v0))
      (coe du_'8743''45'identity'691'_3414 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-identityʳ
d_'8744''45'identity'691'_3422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8744''45'identity'691'_3422 ~v0 ~v1 v2 v3
  = du_'8744''45'identity'691'_3422 v2 v3
du_'8744''45'identity'691'_3422 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8744''45'identity'691'_3422 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v2
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
            v1 v1
            (let v2
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v2
                                 = coe
                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                     (coe v0) in
                           coe
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                   (coe v2))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v2))
                  (coe v1)))
            (let v2
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (let v3
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe v2) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3012
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                     v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))))
         (let v2
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0)) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v2))
               (coe v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))
                     v1)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-identityˡ
d_'8744''45'identity'737'_3426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8744''45'identity'737'_3426 ~v0 ~v1 v2
  = du_'8744''45'identity'737'_3426 v2
du_'8744''45'identity'737'_3426 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8744''45'identity'737'_3426 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'id'691''8658'id'737'_346
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe du_'8744''45'identity'691'_3422 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-identity
d_'8744''45'identity_3428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'identity_3428 ~v0 ~v1 v2
  = du_'8744''45'identity_3428 v2
du_'8744''45'identity_3428 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8744''45'identity_3428 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8744''45'identity'737'_3426 (coe v0))
      (coe du_'8744''45'identity'691'_3422 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-zeroʳ
d_'8743''45'zero'691'_3430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8743''45'zero'691'_3430 ~v0 ~v1 v2 v3
  = du_'8743''45'zero'691'_3430 v2 v3
du_'8743''45'zero'691'_3430 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8743''45'zero'691'_3430 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v2
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v2
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v2
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v2
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v2)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                  (let v2
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v2
                                       = coe
                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                           (coe v0) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                         (coe v2))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))
                     v1))
               (let v2
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (let v3
                         = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                             (coe v2) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v1)
                        (coe v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_3182
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                 (coe v0)))
                           (coe v1))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))))
               v1 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
         (let v2
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (let v3
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                  (coe v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))
                     v1)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-zeroˡ
d_'8743''45'zero'737'_3434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8743''45'zero'737'_3434 ~v0 ~v1 v2
  = du_'8743''45'zero'737'_3434 v2
du_'8743''45'zero'737'_3434 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8743''45'zero'737'_3434 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'691''8658'ze'737'_366
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe du_'8743''45'zero'691'_3430 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-zero
d_'8743''45'zero_3436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'zero_3436 ~v0 ~v1 v2 = du_'8743''45'zero_3436 v2
du_'8743''45'zero_3436 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'zero_3436 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8743''45'zero'737'_3434 (coe v0))
      (coe du_'8743''45'zero'691'_3430 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-zeroʳ
d_'8744''45'zero'691'_3440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8744''45'zero'691'_3440 ~v0 ~v1 v2 v3
  = du_'8744''45'zero'691'_3440 v2 v3
du_'8744''45'zero'691'_3440 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8744''45'zero'691'_3440 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v2
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v2
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v2
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v2
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v2)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v2
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v2)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (let v2
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v2
                                       = coe
                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                           (coe v0) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                         (coe v2))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3196
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))
                     v1))
               (let v2
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (let v3
                         = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                             (coe v2) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v1)
                        (coe v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'idem_3206
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                 (coe v0)))
                           (coe v1))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))))
               v1 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
         (let v2
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (let v3
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                  (coe v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3196
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))
                     v1)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-zeroˡ
d_'8744''45'zero'737'_3444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8744''45'zero'737'_3444 ~v0 ~v1 v2
  = du_'8744''45'zero'737'_3444 v2
du_'8744''45'zero'737'_3444 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8744''45'zero'737'_3444 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'691''8658'ze'737'_366
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe du_'8744''45'zero'691'_3440 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-zero
d_'8744''45'zero_3446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'zero_3446 ~v0 ~v1 v2 = du_'8744''45'zero_3446 v2
du_'8744''45'zero_3446 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8744''45'zero_3446 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8744''45'zero'737'_3444 (coe v0))
      (coe du_'8744''45'zero'691'_3440 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-⊥-isMonoid
d_'8744''45''8869''45'isMonoid_3448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8744''45''8869''45'isMonoid_3448 ~v0 ~v1 v2
  = du_'8744''45''8869''45'isMonoid_3448 v2
du_'8744''45''8869''45'isMonoid_3448 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8744''45''8869''45'isMonoid_3448 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isSemigroup_3212
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
               (coe v0))))
      (coe du_'8744''45'identity_3428 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-⊤-isMonoid
d_'8743''45''8868''45'isMonoid_3450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8743''45''8868''45'isMonoid_3450 ~v0 ~v1 v2
  = du_'8743''45''8868''45'isMonoid_3450 v2
du_'8743''45''8868''45'isMonoid_3450 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8743''45''8868''45'isMonoid_3450 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isSemigroup_3188
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
               (coe v0))))
      (coe du_'8743''45'identity_3420 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-⊥-isCommutativeMonoid
d_'8744''45''8869''45'isCommutativeMonoid_3452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'8744''45''8869''45'isCommutativeMonoid_3452 ~v0 ~v1 v2
  = du_'8744''45''8869''45'isCommutativeMonoid_3452 v2
du_'8744''45''8869''45'isCommutativeMonoid_3452 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_'8744''45''8869''45'isCommutativeMonoid_3452 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe du_'8744''45''8869''45'isMonoid_3448 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-⊤-isCommutativeMonoid
d_'8743''45''8868''45'isCommutativeMonoid_3454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'8743''45''8868''45'isCommutativeMonoid_3454 ~v0 ~v1 v2
  = du_'8743''45''8868''45'isCommutativeMonoid_3454 v2
du_'8743''45''8868''45'isCommutativeMonoid_3454 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_'8743''45''8868''45'isCommutativeMonoid_3454 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe du_'8743''45''8868''45'isMonoid_3450 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-∧-isSemiring
d_'8744''45''8743''45'isSemiring_3456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_'8744''45''8743''45'isSemiring_3456 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isSemiring_3456 v2
du_'8744''45''8743''45'isSemiring_3456 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
du_'8744''45''8743''45'isSemiring_3456 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_48071
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811
         (coe du_'8744''45''8869''45'isCommutativeMonoid_3452 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0)))))
         (coe du_'8743''45'identity_3420 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3052
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe du_'8743''45'zero_3436 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-isSemiring
d_'8743''45''8744''45'isSemiring_3458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_'8743''45''8744''45'isSemiring_3458 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isSemiring_3458 v2
du_'8743''45''8744''45'isSemiring_3458 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
du_'8743''45''8744''45'isSemiring_3458 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_48071
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811
         (coe du_'8743''45''8868''45'isCommutativeMonoid_3454 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0)))))
         (coe du_'8744''45'identity_3428 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3050
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe du_'8744''45'zero_3446 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-∧-isCommutativeSemiring
d_'8744''45''8743''45'isCommutativeSemiring_3460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'8744''45''8743''45'isCommutativeSemiring_3460 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isCommutativeSemiring_3460 v2
du_'8744''45''8743''45'isCommutativeSemiring_3460 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
du_'8744''45''8743''45'isCommutativeSemiring_3460 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51895
      (coe du_'8744''45''8743''45'isSemiring_3456 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-isCommutativeSemiring
d_'8743''45''8744''45'isCommutativeSemiring_3462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'8743''45''8744''45'isCommutativeSemiring_3462 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isCommutativeSemiring_3462 v2
du_'8743''45''8744''45'isCommutativeSemiring_3462 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
du_'8743''45''8744''45'isCommutativeSemiring_3462 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51895
      (coe du_'8743''45''8744''45'isSemiring_3458 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-∧-commutativeSemiring
d_'8744''45''8743''45'commutativeSemiring_3464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'8744''45''8743''45'commutativeSemiring_3464 ~v0 ~v1 v2
  = du_'8744''45''8743''45'commutativeSemiring_3464 v2
du_'8744''45''8743''45'commutativeSemiring_3464 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
du_'8744''45''8743''45'commutativeSemiring_3464 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_44731
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe du_'8744''45''8743''45'isCommutativeSemiring_3460 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-commutativeSemiring
d_'8743''45''8744''45'commutativeSemiring_3466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'8743''45''8744''45'commutativeSemiring_3466 ~v0 ~v1 v2
  = du_'8743''45''8744''45'commutativeSemiring_3466 v2
du_'8743''45''8744''45'commutativeSemiring_3466 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
du_'8743''45''8744''45'commutativeSemiring_3466 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_44731
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe du_'8743''45''8744''45'isCommutativeSemiring_3462 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.lemma
d_lemma_3472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma_3472 ~v0 ~v1 v2 v3 v4 v5 v6 = du_lemma_3472 v2 v3 v4 v5 v6
du_lemma_3472 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma_3472 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5))))))
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
               v2
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v5
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v5)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                  v2
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v5
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v5)))))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v5
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v5))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                     v2
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v5
                                        = coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                            (coe v0) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                          (coe v5)))))))
                        (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v5
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v5))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                           v2)
                        v2
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v5
                                           = coe
                                               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                               (coe v0) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                             (coe v5)))))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                              v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)) v2)
                           v2
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v5
                                              = coe
                                                  MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                  (coe v0) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                (coe v5)))))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)) v2)
                              v2 v2
                              (let v5
                                     = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                            (let v5
                                                   = coe
                                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                       (coe v0) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                  (coe
                                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                     (coe v5))))) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                       (coe v5))
                                    (coe v2)))
                              (coe du_'8743''45'identity'737'_3418 v0 v2))
                           (let v5
                                  = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                         (coe v0)) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                    (coe v5))
                                 (coe v2)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3196
                                    (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                       (coe v0))
                                    v1))))
                        (let v5
                               = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3100
                              (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                 (coe v5))
                              v2 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))))
                     (let v5
                            = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                (coe v0) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                   (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v6))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                              (coe v3)))))
                  (let v5
                         = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                (coe v0)) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'737'_3198
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))
                           v1))))
               (let v5
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3098
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe v5))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1
                     v2)))
            (let v5
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (let v6
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe v5) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v6))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                     (coe v4)))))
         (coe
            du_'8743''45'identity'691'_3414 (coe v0)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra.⊥≉⊤
d_'8869''8777''8868'_3482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny
d_'8869''8777''8868'_3482 ~v0 ~v1 v2
  = du_'8869''8777''8868'_3482 v2
du_'8869''8777''8868'_3482 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny
du_'8869''8777''8868'_3482 v0
  = coe
      du_lemma_3472 (coe v0)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe
         du_'8743''45'identity'691'_3414 (coe v0)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
      (coe
         du_'8744''45'zero'691'_3440 (coe v0)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
-- Algebra.Lattice.Properties.BooleanAlgebra.⊤≉⊥
d_'8868''8777''8869'_3484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny
d_'8868''8777''8869'_3484 ~v0 ~v1 v2
  = du_'8868''8777''8869'_3484 v2
du_'8868''8777''8869'_3484 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny
du_'8868''8777''8869'_3484 v0
  = coe
      du_lemma_3472 (coe v0)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe
         du_'8743''45'zero'691'_3430 (coe v0)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
      (coe
         du_'8744''45'identity'691'_3422 (coe v0)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
-- Algebra.Lattice.Properties.BooleanAlgebra.¬-involutive
d_'172''45'involutive_3486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'172''45'involutive_3486 ~v0 ~v1 v2 v3
  = du_'172''45'involutive_3486 v2 v3
du_'172''45'involutive_3486 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'172''45'involutive_3486 v0 v1
  = coe
      du_lemma_3472 (coe v0)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
      (coe v1)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'737'_3198
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0))
         v1)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3194
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0))
         v1)
-- Algebra.Lattice.Properties.BooleanAlgebra.deMorgan₁
d_deMorgan'8321'_3494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_deMorgan'8321'_3494 ~v0 ~v1 v2 v3 v4
  = du_deMorgan'8321'_3494 v2 v3 v4
du_deMorgan'8321'_3494 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_deMorgan'8321'_3494 v0 v1 v2
  = coe
      du_lemma_3472 (coe v0)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
      (coe du_lem'8321'_3504 (coe v0) (coe v1) (coe v2))
      (coe du_lem'8322'_3508 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra._.lem₁
d_lem'8321'_3504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lem'8321'_3504 ~v0 ~v1 v2 v3 v4 = du_lem'8321'_3504 v2 v3 v4
du_lem'8321'_3504 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8321'_3504 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v3)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v3
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v3)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v3
                                        = coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                            (coe v0) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                          (coe v3)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                        (let v3
                               = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v3
                                             = coe
                                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                 (coe v0) in
                                       coe
                                         (coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                            (coe
                                               MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                               (coe v3))))) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                 (coe v3))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
                        (coe
                           du_'8744''45'identity'691'_3422 (coe v0)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe du_'8743''45'zero'691'_3430 (coe v0) (coe v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                        (coe du_'8743''45'zero'691'_3430 (coe v0) (coe v1))))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (let v3
                            = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                   (coe v0)) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                           (coe v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))
                              v1)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2)
                           (\ v3 v4 -> v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v3 v4 -> v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1)
                           (\ v3 v4 -> v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v3 v4 -> v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
                     (let v3
                            = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                   (coe v0)) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                           (coe v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))
                              v2)))))
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v2 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v1 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
            (let v3
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                          (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                     (\ v4 v5 -> v4)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5)
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                          (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1))
                  (let v4
                         = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                (coe v0)) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v4))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                    (coe v0))))
                           v1 v2))))))
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3098
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe v3))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.lem₃
d_lem'8323'_3506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lem'8323'_3506 ~v0 ~v1 v2 v3 v4 = du_lem'8323'_3506 v2 v3 v4
du_lem'8323'_3506 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8323'_3506 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v3)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (let v3
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v3
                                       = coe
                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                           (coe v0) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                         (coe v3))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v2 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
               (coe
                  du_'8743''45'identity'737'_3418 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))))
            (let v3
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3196
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))
                     v1))))
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3096
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe v3))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1
               v2)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.lem₂
d_lem'8322'_3508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322'_3508 ~v0 ~v1 v2 v3 v4 = du_lem'8322'_3508 v2 v3 v4
du_lem'8322'_3508 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322'_3508 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v3
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v3)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v3
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v3)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                     (let v3
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v3
                                          = coe
                                              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                              (coe v0) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                         (coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                            (coe v3))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v3))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))))
                     (coe
                        du_'8744''45'zero'691'_3440 (coe v0)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
                  (let v3
                         = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                (coe v0)) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3196
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))
                           v2))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (let v3
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (let v4
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v4))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe du_lem'8323'_3506 (coe v0) (coe v1) (coe v2))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0))))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
-- Algebra.Lattice.Properties.BooleanAlgebra.deMorgan₂
d_deMorgan'8322'_3514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_deMorgan'8322'_3514 ~v0 ~v1 v2 v3 v4
  = du_deMorgan'8322'_3514 v2 v3 v4
du_deMorgan'8322'_3514 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_deMorgan'8322'_3514 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v3
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (let v3
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v3
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v3))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
               (coe
                  du_'172''45'involutive_3486 (coe v0)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               (coe
                  du_deMorgan'8321'_3494 (coe v0)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe du_'172''45'involutive_3486 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  v2)
               (coe du_'172''45'involutive_3486 (coe v0) (coe v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._⊕_
d__'8853'__3530 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d__'8853'__3530 ~v0 v1 ~v2 = du__'8853'__3530 v1
du__'8853'__3530 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'8853'__3530 v0 = coe v0
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.helper
d_helper_3540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_helper_3540 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_helper_3540 v2 v5 v6 v7 v8 v9 v10
du_helper_3540 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_helper_3540 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240 (coe v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
         (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0))))
         v1 v2
         (coe
            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
            (\ v7 v8 -> v7) v3 v4)
         (coe
            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
            (\ v7 v8 -> v8)
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0)) v3
            v4))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0))
         v3 v4 v6)
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-cong
d_'8853''45'cong_3546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'cong_3546 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_'8853''45'cong_3546 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_'8853''45'cong_3546 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'cong_3546 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v9 v10 v11 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v11)
      (coe v1 v3 v5) (coe v1 v4 v6)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v9)))))))
         (coe v1 v3 v5)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v5)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5)))
         (coe v1 v4 v6)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v9
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v9)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v6)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v6)))
            (coe v1 v4 v6)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v9
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v9)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v9
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v9))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v6)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v6)))
               (coe v1 v4 v6) (coe v1 v4 v6)
               (let v9
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v9
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v9))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v9))
                     (coe v1 v4 v6)))
               (coe v2 v4 v6))
            (coe
               du_helper_3540 (coe v0)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v5)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v6)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v6)
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240 (coe v7)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v3 v4 v5 v6)
                  (coe v8))
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240 (coe v7)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v3 v4 v5 v6)
                  (coe v8))))
         (coe v2 v3 v5))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-comm
d_'8853''45'comm_3560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'comm_3560 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'8853''45'comm_3560 v2 v3 v4 v5 v6
du_'8853''45'comm_3560 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'comm_3560 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe v1 v3 v4) (coe v1 v4 v3)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
         (coe v1 v3 v4)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
         (coe v1 v4 v3)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))
            (coe v1 v4 v3)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))
               (coe v1 v4 v3) (coe v1 v4 v3)
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v5
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v5))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v5))
                     (coe v1 v4 v3)))
               (coe v2 v4 v3))
            (coe
               du_helper_3540 (coe v0)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  v3 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  v3 v4)))
         (coe v2 v3 v4))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.¬-distribˡ-⊕
d_'172''45'distrib'737''45''8853'_3570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'distrib'737''45''8853'_3570 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'172''45'distrib'737''45''8853'_3570 v2 v3 v4 v5 v6
du_'172''45'distrib'737''45''8853'_3570 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'172''45'distrib'737''45''8853'_3570 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
         (coe v1 v3 v4))
      (coe
         v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
         v4)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe v1 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4))))
         (coe
            v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
            v4)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))))
            (coe
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
               v4)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                  v4)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v5
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v5)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                  (coe
                     v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                     v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v5
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v5)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                     (coe
                        v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                        v4)
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v5
                                        = coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                            (coe v0) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                          (coe v5)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                        (coe
                           v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                           v4)
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v5
                                           = coe
                                               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                               (coe v0) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                             (coe v5)))))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3) v4)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                    v4)))
                           (coe
                              v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                              v4)
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v5
                                              = coe
                                                  MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                  (coe v0) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                (coe v5)))))))
                              (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v5
                                           = coe
                                               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                               (coe v0) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                             (coe v5))))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                    v4)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       v4)))
                              (coe
                                 v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 v4)
                              (coe
                                 v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 v4)
                              (let v5
                                     = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                            (let v5
                                                   = coe
                                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                       (coe v0) in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                  (coe
                                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                     (coe v5))))) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                       (coe v5))
                                    (coe
                                       v1
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       v4)))
                              (coe
                                 v2 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 v4))
                           (coe
                              du_helper_3540 (coe v0)
                              (coe
                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                                 (\ v5 v6 -> v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                 v4)
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v5 v6 -> v6)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3) v4)
                              (let v5
                                     = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                         (coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                            (coe v0)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                       (coe v5))
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                    (coe v4) (coe du_'172''45'involutive_3486 (coe v0) (coe v4))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                                 (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                          (coe v0))))
                                 v4 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                        (let v5
                               = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                      (coe v0)) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)))
                              (coe
                                 du_deMorgan'8321'_3494 (coe v0) (coe v3)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)))))
                     (coe
                        du_deMorgan'8322'_3514 (coe v0)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe du_lem_3584 (coe v0) (coe v3) (coe v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                        (coe du_lem_3584 (coe v0) (coe v4) (coe v3)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4))))
                     (\ v5 v6 -> v5)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4)
                        (\ v5 v6 -> v5)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v5 v6 -> v6)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v5 v6 -> v6)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4))))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4)
                        (\ v5 v6 -> v5)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v5 v6 -> v6)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))))
                  (let v5
                         = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                (coe v0)) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4)
                           (\ v6 v7 -> v6)
                           (coe
                              MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                              (\ v6 v7 -> v6)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))
                           (coe
                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                              (\ v6 v7 -> v7)
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v6 v7 -> v7)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4)
                           (coe
                              MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                              (\ v6 v7 -> v6)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))
                           (coe
                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                              (\ v6 v7 -> v7)
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)))
                        (let v6
                               = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                      (coe v0)) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v6))
                              (coe v4)
                              (coe
                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                                 (\ v7 v8 -> v7)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v7 v8 -> v8)
                                 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
                                 (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                    (coe v0))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                                    (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                             (coe v0))))
                                    v3 v4))))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4))))
               (let v5
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3100
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe v5))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4))
                     v3 v4))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))
            (coe v1 v3 v4)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)))
            (coe v2 v3 v4)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem
d_lem_3584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem_3584 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 = du_lem_3584 v2 v7 v8
du_lem_3584 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem_3584 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v3)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (let v3
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v3
                                       = coe
                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                           (coe v0) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                         (coe v3))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
                  (coe
                     du_'8744''45'identity'737'_3426 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
               (let v3
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                             (coe v0)) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))
                        v1))))
            (let v3
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3098
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                     (coe v3))
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))))
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0)) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
               (coe v1)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe du_deMorgan'8321'_3494 (coe v0) (coe v1) (coe v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.¬-distribʳ-⊕
d_'172''45'distrib'691''45''8853'_3594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'distrib'691''45''8853'_3594 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'172''45'distrib'691''45''8853'_3594 v2 v3 v4 v5 v6
du_'172''45'distrib'691''45''8853'_3594 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'172''45'distrib'691''45''8853'_3594 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
         (coe v1 v3 v4))
      (coe
         v1 v3
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe v1 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe v1 v4 v3))
         (coe
            v1 v3
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe v1 v4 v3))
            (coe
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
               v3)
            (coe
               v1 v3
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                  v3)
               (coe
                  v1 v3
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
               (coe
                  v1 v3
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v5
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v5))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v5))
                     (coe
                        v1 v3
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))))
               (coe
                  du_'8853''45'comm_3560 (coe v0) (coe v1) (coe v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                  (coe v3)))
            (coe
               du_'172''45'distrib'737''45''8853'_3570 (coe v0) (coe v1) (coe v2)
               (coe v4) (coe v3)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))
            (coe v1 v3 v4) (coe v1 v4 v3)
            (coe
               du_'8853''45'comm_3560 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-annihilates-¬
d_'8853''45'annihilates'45''172'_3604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'annihilates'45''172'_3604 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'8853''45'annihilates'45''172'_3604 v2 v3 v4 v5 v6
du_'8853''45'annihilates'45''172'_3604 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'annihilates'45''172'_3604 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe v1 v3 v4)
      (coe
         v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5))))))
         (coe v1 v3 v4)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe v1 v3 v4)))
         (coe
            v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe v1 v3 v4)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                  v4))
            (coe
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                     v4))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v5
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v5))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v5))
                     (coe
                        v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))))
               (coe
                  du_'172''45'distrib'691''45''8853'_3594 (coe v0) (coe v1) (coe v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                  (coe v4)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe v1 v3 v4))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                  v4)
               (coe
                  du_'172''45'distrib'737''45''8853'_3570 (coe v0) (coe v1) (coe v2)
                  (coe v3) (coe v4))))
         (coe du_'172''45'involutive_3486 (coe v0) (coe v1 v3 v4)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-identityˡ
d_'8853''45'identity'737'_3610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8853''45'identity'737'_3610 ~v0 ~v1 v2 v3 v4 v5
  = du_'8853''45'identity'737'_3610 v2 v3 v4 v5
du_'8853''45'identity'737'_3610 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8853''45'identity'737'_3610 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         v1 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)
      v3
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (coe
            v1 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)))
         v3
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
            v3
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
               v3
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v4)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
                  v3 v3
                  (let v4
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v4
                                       = coe
                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                           (coe v0) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                         (coe v4))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v4))
                        (coe v3)))
                  (coe du_'8743''45'identity'691'_3414 (coe v0) (coe v3)))
               (let v4
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                             (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                        (coe v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                        (coe du_'8869''8777''8868'_3482 (coe v0))))))
            (coe
               du_helper_3540 (coe v0)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)
               (coe v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
               (coe du_'8744''45'identity'737'_3426 v0 v3)
               (coe du_'8743''45'zero'737'_3434 v0 v3)))
         (coe
            v2 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
            v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-identityʳ
d_'8853''45'identity'691'_3614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8853''45'identity'691'_3614 ~v0 ~v1 v2 v3 v4 v5
  = du_'8853''45'identity'691'_3614 v2 v3 v4 v5
du_'8853''45'identity'691'_3614 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8853''45'identity'691'_3614 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
      (coe
         du_'8853''45'comm_3560 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0)))))
         (coe
            v1 v3 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
         (coe
            v1 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)) v3)
         v3)
      (coe
         du_'8853''45'identity'737'_3610 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-identity
d_'8853''45'identity_3616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'identity_3616 ~v0 ~v1 v2 v3 v4
  = du_'8853''45'identity_3616 v2 v3 v4
du_'8853''45'identity_3616 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'identity_3616 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8853''45'identity'737'_3610 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'identity'691'_3614 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-inverseˡ
d_'8853''45'inverse'737'_3618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8853''45'inverse'737'_3618 ~v0 ~v1 v2 v3 v4 v5
  = du_'8853''45'inverse'737'_3618 v2 v3 v4 v5
du_'8853''45'inverse'737'_3618 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8853''45'inverse'737'_3618 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe v1 v3 v3)
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (coe v1 v3 v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v3)))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v4))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0))
                  v3))
            (coe
               du_helper_3540 (coe v0)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v3)
               (coe v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v3)
               (coe v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'idem_3206
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                        (coe v0)))
                  (coe v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_3182
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                        (coe v0)))
                  (coe v3))))
         (coe v2 v3 v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-inverseʳ
d_'8853''45'inverse'691'_3622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8853''45'inverse'691'_3622 ~v0 ~v1 v2 v3 v4 v5
  = du_'8853''45'inverse'691'_3622 v2 v3 v4 v5
du_'8853''45'inverse'691'_3622 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8853''45'inverse'691'_3622 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
      (coe
         du_'8853''45'comm_3560 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0)))))
         (coe v1 v3 v3) (coe v1 v3 v3)
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
      (coe
         du_'8853''45'inverse'737'_3618 (coe v0) (coe v1) (coe v2) (coe v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-inverse
d_'8853''45'inverse_3624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'inverse_3624 ~v0 ~v1 v2 v3 v4
  = du_'8853''45'inverse_3624 v2 v3 v4
du_'8853''45'inverse_3624 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'inverse_3624 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8853''45'inverse'737'_3618 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'inverse'691'_3622 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.∧-distribˡ-⊕
d_'8743''45'distrib'737''45''8853'_3626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8853'_3626 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8743''45'distrib'737''45''8853'_3626 v2 v3 v4 v5 v6 v7
du_'8743''45'distrib'737''45''8853'_3626 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8853'_3626 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v6 v7 v8 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
         (coe v1 v4 v5))
      (coe
         v1
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v6
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v6)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
            (coe v1 v4 v5))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))
         (coe
            v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v6
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v6)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v6
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v6))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5)))
            (coe
               v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v6
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v6)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
               (coe
                  v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v6
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v6)))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v6
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v6))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                  (coe
                     v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v6
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v6)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                     (coe
                        v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v6
                                        = coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                            (coe v0) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                          (coe v6)))))))
                        (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v6
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v6))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                        (coe
                           v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v6
                                           = coe
                                               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                               (coe v0) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                             (coe v6)))))))
                           (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v6
                                        = coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                            (coe v0) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                          (coe v6))))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                       v5))))
                           (coe
                              v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v6
                                              = coe
                                                  MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                  (coe v0) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                (coe v6)))))))
                              (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v6
                                           = coe
                                               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                               (coe v0) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                             (coe v6))))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                          v5))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                          v5))))
                              (coe
                                 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v5))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (let v6
                                                 = coe
                                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                     (coe v0) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                   (coe v6)))))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v4 v5))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v5))))
                                 (coe
                                    v1
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                       v5))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (let v6
                                                    = coe
                                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                        (coe v0) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                      (coe v6)))))))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v4 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v5))))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v5))))
                                    (coe
                                       v1
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                          v5))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                (let v6
                                                       = coe
                                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                           (coe v0) in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                      (coe
                                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                         (coe v6)))))))
                                       (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (let v6
                                                    = coe
                                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                        (coe v0) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                      (coe v6))))))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v5))
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                   v0 v3 v4)
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                   v0 v3 v5))))
                                       (coe
                                          v1
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v5))
                                       (coe
                                          v1
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v5))
                                       (let v6
                                              = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                     (let v6
                                                            = coe
                                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                                (coe v0) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                           (coe
                                                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                              (coe v6))))) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                                (coe v6))
                                             (coe
                                                v1
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                   v0 v3 v4)
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                   v0 v3 v5))))
                                       (coe
                                          v2
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v5)))
                                    (let v6
                                           = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                               (coe
                                                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                                  (coe v0)) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                             (coe v6))
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                   v0 v3 v4)
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                   v0 v3 v5)))
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708
                                                v0 v4 v5))
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v5))
                                          (let v7
                                                 = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                                     (coe v0) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3098
                                                (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                                   (coe v7))
                                                v3 v4 v5)))))
                                 (coe
                                    du_helper_3540 (coe v0)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                          v5))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                                   (coe v0)))))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v4 v5)))
                                    (coe du_lem'8321'_3640 (coe v0) (coe v3) (coe v4) (coe v5))))
                              (let v6
                                     = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                         (coe v0) in
                               coe
                                 (let v7
                                        = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                            (coe v6) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                          (coe v7))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v4 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v4 v5)))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v3)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v4 v5)))
                                       (coe
                                          du_deMorgan'8321'_3494 (coe v0) (coe v3)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v4 v5))))))
                           (let v6
                                  = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                         (coe v0)) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                    (coe v6))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                                    (\ v7 v8 -> v7)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                                 (coe
                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                    (\ v7 v8 -> v8)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                                 (let v7
                                        = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                            (coe v0) in
                                  coe
                                    (let v8
                                           = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                               (coe v7) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                             (coe v8))
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v3)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v4 v5))
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                                v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                                v5))
                                          (coe
                                             du_deMorgan'8321'_3494 (coe v0) (coe v4)
                                             (coe v5))))))))
                        (let v6
                               = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3098
                              (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                 (coe v6))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))))
                     (let v6
                            = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                (coe v0) in
                      coe
                        (let v7
                               = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                   (coe v6) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v7))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4
                                       v5))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                              (coe du_lem'8323'_3642 (coe v0) (coe v3) (coe v4) (coe v5))))))
                  (coe
                     du_'8744''45'identity'737'_3426 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))))
               (let v6
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                             (coe v0)) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v6))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                     (coe du_deMorgan'8321'_3494 (coe v0) (coe v4) (coe v5)))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))))
               v3
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))
         (let v6
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0)) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v6))
               (coe v3) (coe v1 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5)))
               (coe v2 v4 v5))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₂
d_lem'8322'_3638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322'_3638 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8322'_3638 v2 v5 v6 v7
du_lem'8322'_3638 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322'_3638 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v4
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v4))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  v2 v1 v3))
            (let v4
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v4))
                  (coe v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v1 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0))))
            v1 v2 v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₁
d_lem'8321'_3640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8321'_3640 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8321'_3640 v2 v5 v6 v7
du_lem'8321'_3640 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8321'_3640 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v4
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v4)))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
                  (let v4
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v4
                                       = coe
                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                           (coe v0) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                         (coe v4))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v1 v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3)))
               (let v4
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                             (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                        (coe v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v3))
                        (coe du_lem'8322'_3638 (coe v0) (coe v1) (coe v2) (coe v3))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))))
               v1 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)))
         (let v4
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (let v5
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe v4) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v1)
                  (coe v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_3182
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                           (coe v0)))
                     (coe v1))))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₃
d_lem'8323'_3642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8323'_3642 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8323'_3642 v2 v5 v6 v7
du_lem'8323'_3642 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8323'_3642 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v4
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                     v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v4)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                        v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                  (let v4
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v4
                                       = coe
                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                           (coe v0) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                         (coe v4))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))))
                  (let v4
                         = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                             (coe v0) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                              v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                       (coe v0))))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                              v1)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)))
            (let v4
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))
                        v1)))))
         (coe
            du_'8743''45'zero'691'_3430 (coe v0)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.∧-distribʳ-⊕
d_'8743''45'distrib'691''45''8853'_3644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8853'_3644 ~v0 ~v1 v2 v3 v4
  = du_'8743''45'distrib'691''45''8853'_3644 v2 v3 v4
du_'8743''45'distrib'691''45''8853'_3644 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8853'_3644 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'737''8658'distr'691'_504
      (let v3
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 (coe v0))
      (coe v1) (coe du_'8853''45'cong_3546 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe
         du_'8743''45'distrib'737''45''8853'_3626 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.∧-distrib-⊕
d_'8743''45'distrib'45''8853'_3646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8853'_3646 ~v0 ~v1 v2 v3 v4
  = du_'8743''45'distrib'45''8853'_3646 v2 v3 v4
du_'8743''45'distrib'45''8853'_3646 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'distrib'45''8853'_3646 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8743''45'distrib'737''45''8853'_3626 (coe v0) (coe v1)
         (coe v2))
      (coe
         du_'8743''45'distrib'691''45''8853'_3644 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.lemma₂
d_lemma'8322'_3656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8322'_3656 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_lemma'8322'_3656 v2 v5 v6 v7 v8
du_lemma'8322'_3656 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8322'_3656 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v3)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v4)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v4)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v4)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                  v4))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v4)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v4)))
            (let v5
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v5
                                 = coe
                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                     (coe v0) in
                           coe
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                   (coe v5))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v5))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v3)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v4)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v4)))))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (let v5
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3096
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe v5))
                     v3 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v3)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v4)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v4)))
               (let v5
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3096
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe v5))
                     v4 v1 v2))))
         (let v5
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3094
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe v5))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
               v3 v4)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-assoc
d_'8853''45'assoc_3666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'assoc_3666 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8853''45'assoc_3666 v2 v3 v4 v5 v6 v7
du_'8853''45'assoc_3666 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'assoc_3666 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe v1 v3 (coe v1 v4 v5)) (coe v1 (coe v1 v3 v4) v5)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v6 v7 v8 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
         (coe v1 v3 (coe v1 v4 v5)) (coe v1 (coe v1 v3 v4) v5)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v6
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v6)))))))
            (coe v1 v3 (coe v1 v4 v5))
            (coe
               v1 v3
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))
            (coe v1 (coe v1 v3 v4) v5)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v6
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v6)))))))
               (coe
                  v1 v3
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))))
               (coe v1 (coe v1 v3 v4) v5)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v6
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v6)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                    v5))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3) v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                  (coe v1 (coe v1 v3 v4) v5)
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v6
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v6)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3) v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                    v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))))
                     (coe v1 (coe v1 v3 v4) v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v6
                                        = coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                            (coe v0) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                          (coe v6)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       v4)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       v4)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))))
                        (coe v1 (coe v1 v3 v4) v5)
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v6
                                           = coe
                                               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                               (coe v0) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                             (coe v6)))))))
                           (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v6
                                        = coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                            (coe v0) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                          (coe v6))))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v4))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v3)
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          v5)))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                    v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))))
                           (coe v1 (coe v1 v3 v4) v5)
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v6
                                              = coe
                                                  MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                  (coe v0) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                (coe v6)))))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          v4)
                                       v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v3)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v4))
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v4))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v3)
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          v5))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)))
                                       v5)))
                              (coe v1 (coe v1 v3 v4) v5)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (let v6
                                                 = coe
                                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                     (coe v0) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                   (coe v6)))))))
                                 (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v6
                                              = coe
                                                  MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                  (coe v0) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                (coe v6))))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)))
                                       v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                   v0 v3 v4)))
                                          v5)))
                                 (coe
                                    v1
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)))
                                    v5)
                                 (coe v1 (coe v1 v3 v4) v5)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (let v6
                                                    = coe
                                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                        (coe v0) in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                      (coe v6)))))))
                                    (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (let v6
                                                 = coe
                                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                     (coe v0) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                   (coe v6))))))
                                    (coe
                                       v1
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)))
                                       v5)
                                    (coe v1 (coe v1 v3 v4) v5) (coe v1 (coe v1 v3 v4) v5)
                                    (let v6
                                           = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                  (let v6
                                                         = coe
                                                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                                             (coe v0) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                                        (coe
                                                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                                           (coe v6))))) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                             (coe v6))
                                          (coe v1 (coe v1 v3 v4) v5)))
                                    (coe
                                       du_'8853''45'cong_3546 (coe v0) (coe v1) (coe v2)
                                       (coe v1 v3 v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)))
                                       (coe v5) (coe v5) (coe v2 v3 v4)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                                      (coe v0)))))
                                          v5)))
                                 (coe
                                    v2
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)))
                                    v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                                 (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                          (coe v0))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          v4)
                                       v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v3)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v4))
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                             v3 v4)))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v4))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v3)
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
                                                v0 v3 v4)))
                                       v5))
                                 (coe du_lem'8321'_3678 (coe v0) (coe v3) (coe v4) (coe v5))
                                 (coe du_lem'8322'_3682 (coe v0) (coe v3) (coe v4) (coe v5))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
                              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                       (coe v0))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                       v4)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))))
                        (let v6
                               = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                   (coe v0) in
                         coe
                           (let v7
                                  = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                      (coe v6) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                                    (coe v7))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v4))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                                v3)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                                v4))
                                          v5)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                                v3)
                                             v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v5))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v3)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v4))
                                       v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             v3
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                                v4))
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                                v3)
                                             v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                             v5))))
                                 (coe du_lem'8325'_3690 (coe v0) (coe v3) (coe v4) (coe v5))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3) v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3 v4)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4
                                    v5)))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v4))
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3) v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v5)))
                     (coe du_lem'8323'_3684 (coe v0) (coe v3) (coe v4) (coe v5))
                     (coe du_lem'8324'_3688 (coe v0) (coe v3) (coe v4) (coe v5))))
               (coe
                  v2 v3
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5)))))
            (coe
               du_'8853''45'cong_3546 (coe v0) (coe v1) (coe v2) (coe v3) (coe v3)
               (coe v1 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v4 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v4 v5)))
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0)))))
                  v3)
               (coe v2 v4 v5))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₁
d_lem'8321'_3678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8321'_3678 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8321'_3678 v2 v5 v6 v7
du_lem'8321'_3678 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8321'_3678 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            v3))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
         v3)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v4
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
            v3)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
               v3)
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v4
                                 = coe
                                     MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                     (coe v0) in
                           coe
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                   (coe v4))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v4))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
                     v3)))
            (let v4
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v4))
                  (coe v3)
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
                     (\ v5 v6 -> v5)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v5 v6 -> v6)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                  (let v5
                         = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                             (coe v0) in
                   coe
                     (let v6
                            = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v6))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           (coe du_deMorgan'8321'_3494 (coe v0) (coe v1) (coe v2))))))))
         (let v4
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3096
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe v4))
               v3
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₂′
d_lem'8322''8242'_3680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322''8242'_3680 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7
  = du_lem'8322''8242'_3680 v2 v5 v6
du_lem'8322''8242'_3680 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322''8242'_3680 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v3
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v3)))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v3
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v3)))))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v3))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
                     (let v3
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v3
                                          = coe
                                              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                              (coe v0) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                         (coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                            (coe v3))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v3))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
                                       v2))))))
                     (coe
                        du_deMorgan'8321'_3494 (coe v0)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)
                     (coe du_deMorgan'8322'_3514 (coe v0) (coe v1) (coe v2))
                     (coe
                        du_'172''45'involutive_3486 (coe v0)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
               (coe
                  du_lemma'8322'_3656 (coe v0)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                  (coe v1) (coe v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                  (\ v3 v4 -> v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v3 v4 -> v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3194
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                        (coe v0))
                     v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1))
               (let v3
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                             (coe v0)) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3194
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))
                        v2)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
            (coe
               du_'8743''45'identity'737'_3418 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
            (coe
               du_'8743''45'identity'691'_3414 (coe v0)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₂
d_lem'8322'_3682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322'_3682 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8322'_3682 v2 v5 v6 v7
du_lem'8322'_3682 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322'_3682 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
            v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v4
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
               v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
                  v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
                     v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
                     v3))
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v4))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
                           v3))))
               (coe
                  du_deMorgan'8321'_3494 (coe v0)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
                  (coe v3)))
            (let v4
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
                     (coe du_lem'8322''8242'_3680 (coe v0) (coe v1) (coe v2))))))
         (let v4
                = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                    (coe v0) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3096
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe v4))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₃
d_lem'8323'_3684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8323'_3684 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8323'_3684 v2 v5 v6 v7
du_lem'8323'_3684 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8323'_3684 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v4))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))))
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v1 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
            (let v4
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3094
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                     (coe v4))
                  v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))))
         (let v4
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0)) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v4))
               (coe v1)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                  (\ v5 v6 -> v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v5 v6 -> v6)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
               (let v5
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                             (coe v0)) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe du_deMorgan'8321'_3494 (coe v0) (coe v2) (coe v3)))))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₄′
d_lem'8324''8242'_3686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8324''8242'_3686 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7
  = du_lem'8324''8242'_3686 v2 v6 v7
du_lem'8324''8242'_3686 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8324''8242'_3686 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v3)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v3)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v3
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v3)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                     (let v3
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v3
                                          = coe
                                              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                              (coe v0) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                         (coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                            (coe v3))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v3))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                                 v2))))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe
                           du_'8743''45'identity'737'_3418 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                        (coe
                           du_'8743''45'identity'691'_3414 (coe v0)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                              v2))))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3194
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))
                           v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                    (coe v0))))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v1))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)))
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                           (\ v3 v4 -> v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v3 v4 -> v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))))
                     (let v3
                            = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                   (coe v0)) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v3))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3194
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))
                              v2)))))
               (coe
                  du_lemma'8322'_3656 (coe v0)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                  (coe v1) (coe v2)))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe du_deMorgan'8322'_3514 (coe v0) (coe v1) (coe v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
               (coe
                  du_'172''45'involutive_3486 (coe v0)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
         (coe
            du_deMorgan'8321'_3494 (coe v0)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₄
d_lem'8324'_3688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8324'_3688 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8324'_3688 v2 v5 v6 v7
du_lem'8324'_3688 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8324'_3688 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v4
                                  = coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                      (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                    (coe v4)))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (let v4
                                     = coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                         (coe v0) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                       (coe v4)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                     (let v4
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v4
                                          = coe
                                              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                              (coe v0) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                         (coe
                                            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                            (coe v4))))) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v4))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                                 v3)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                                    v2)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           v3)))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v3)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                                 (coe v0))))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v3)))
               (let v4
                      = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3094
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe v4))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2)
                        v3))))
            (let v4
                   = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v5))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2) v3))
                     (coe du_lem'8324''8242'_3686 (coe v0) (coe v2) (coe v3))))))
         (coe
            du_deMorgan'8321'_3494 (coe v0) (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v2 v3)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₅
d_lem'8325'_3690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8325'_3690 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8325'_3690 v2 v5 v6 v7
du_lem'8325'_3690 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8325'_3690 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v4
                         = coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                             (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v4
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v4
                            = coe
                                MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v4
                               = coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                   (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v4)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
               (let v4
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v4
                                    = coe
                                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                                        (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
                                      (coe v4))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v4))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
            (let v4
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v4))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
                        v3)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                     (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v2))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 v3))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-isMagma
d_'8853''45'isMagma_3692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8853''45'isMagma_3692 ~v0 ~v1 v2 v3 v4
  = du_'8853''45'isMagma_3692 v2 v3 v4
du_'8853''45'isMagma_3692 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8853''45'isMagma_3692 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe du_'8853''45'cong_3546 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-isSemigroup
d_'8853''45'isSemigroup_3694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8853''45'isSemigroup_3694 ~v0 ~v1 v2 v3 v4
  = du_'8853''45'isSemigroup_3694 v2 v3 v4
du_'8853''45'isSemigroup_3694 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8853''45'isSemigroup_3694 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe du_'8853''45'isMagma_3692 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'assoc_3666 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-⊥-isMonoid
d_'8853''45''8869''45'isMonoid_3696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8853''45''8869''45'isMonoid_3696 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8869''45'isMonoid_3696 v2 v3 v4
du_'8853''45''8869''45'isMonoid_3696 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8853''45''8869''45'isMonoid_3696 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe du_'8853''45'isSemigroup_3694 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'identity_3616 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-⊥-isGroup
d_'8853''45''8869''45'isGroup_3698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_'8853''45''8869''45'isGroup_3698 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8869''45'isGroup_3698 v2 v3 v4
du_'8853''45''8869''45'isGroup_3698 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
du_'8853''45''8869''45'isGroup_3698 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsGroup'46'constructor_26963
      (coe
         du_'8853''45''8869''45'isMonoid_3696 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'inverse_3624 (coe v0) (coe v1) (coe v2))
      (coe (\ v3 v4 v5 -> v5))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-⊥-isAbelianGroup
d_'8853''45''8869''45'isAbelianGroup_3700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'8853''45''8869''45'isAbelianGroup_3700 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8869''45'isAbelianGroup_3700 v2 v3 v4
du_'8853''45''8869''45'isAbelianGroup_3700 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
du_'8853''45''8869''45'isAbelianGroup_3700 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsAbelianGroup'46'constructor_32441
      (coe
         du_'8853''45''8869''45'isGroup_3698 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'comm_3560 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-∧-isRing
d_'8853''45''8743''45'isRing_3702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_'8853''45''8743''45'isRing_3702 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8743''45'isRing_3702 v2 v3 v4
du_'8853''45''8743''45'isRing_3702 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
du_'8853''45''8743''45'isRing_3702 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsRing'46'constructor_95033
      (coe
         du_'8853''45''8869''45'isAbelianGroup_3700 (coe v0) (coe v1)
         (coe v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
      (coe du_'8743''45'identity_3420 (coe v0))
      (coe
         du_'8743''45'distrib'45''8853'_3646 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-∧-isCommutativeRing
d_'8853''45''8743''45'isCommutativeRing_3704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796
d_'8853''45''8743''45'isCommutativeRing_3704 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8743''45'isCommutativeRing_3704 v2 v3 v4
du_'8853''45''8743''45'isCommutativeRing_3704 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796
du_'8853''45''8743''45'isCommutativeRing_3704 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeRing'46'constructor_100945
      (coe du_'8853''45''8743''45'isRing_3702 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-∧-commutativeRing
d_'8853''45''8743''45'commutativeRing_3706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4016
d_'8853''45''8743''45'commutativeRing_3706 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8743''45'commutativeRing_3706 v2 v3 v4
du_'8853''45''8743''45'commutativeRing_3706 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4016
du_'8853''45''8743''45'commutativeRing_3706 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeRing'46'constructor_72553
      v1 (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 (coe v0))
      (\ v3 -> v3)
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0))
      (coe
         du_'8853''45''8743''45'isCommutativeRing_3704 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra._⊕_
d__'8853'__3708 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8853'__3708 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.¬-distribʳ-⊕
d_'172''45'distrib'691''45''8853'_3720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'distrib'691''45''8853'_3720 ~v0 ~v1 v2
  = du_'172''45'distrib'691''45''8853'_3720 v2
du_'172''45'distrib'691''45''8853'_3720 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'172''45'distrib'691''45''8853'_3720 v0
  = coe
      du_'172''45'distrib'691''45''8853'_3594 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.¬-distribˡ-⊕
d_'172''45'distrib'737''45''8853'_3722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'distrib'737''45''8853'_3722 ~v0 ~v1 v2
  = du_'172''45'distrib'737''45''8853'_3722 v2
du_'172''45'distrib'737''45''8853'_3722 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'172''45'distrib'737''45''8853'_3722 v0
  = coe
      du_'172''45'distrib'737''45''8853'_3570 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.∧-distrib-⊕
d_'8743''45'distrib'45''8853'_3724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8853'_3724 ~v0 ~v1 v2
  = du_'8743''45'distrib'45''8853'_3724 v2
du_'8743''45'distrib'45''8853'_3724 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'distrib'45''8853'_3724 v0
  = coe
      du_'8743''45'distrib'45''8853'_3646 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.∧-distribʳ-⊕
d_'8743''45'distrib'691''45''8853'_3726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8853'_3726 ~v0 ~v1 v2
  = du_'8743''45'distrib'691''45''8853'_3726 v2
du_'8743''45'distrib'691''45''8853'_3726 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8853'_3726 v0
  = coe
      du_'8743''45'distrib'691''45''8853'_3644 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.∧-distribˡ-⊕
d_'8743''45'distrib'737''45''8853'_3728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8853'_3728 ~v0 ~v1 v2
  = du_'8743''45'distrib'737''45''8853'_3728 v2
du_'8743''45'distrib'737''45''8853'_3728 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8853'_3728 v0
  = coe
      du_'8743''45'distrib'737''45''8853'_3626 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-annihilates-¬
d_'8853''45'annihilates'45''172'_3730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'annihilates'45''172'_3730 ~v0 ~v1 v2
  = du_'8853''45'annihilates'45''172'_3730 v2
du_'8853''45'annihilates'45''172'_3730 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'annihilates'45''172'_3730 v0
  = coe
      du_'8853''45'annihilates'45''172'_3604 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-assoc
d_'8853''45'assoc_3732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'assoc_3732 ~v0 ~v1 v2 = du_'8853''45'assoc_3732 v2
du_'8853''45'assoc_3732 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'assoc_3732 v0
  = coe
      du_'8853''45'assoc_3666 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-comm
d_'8853''45'comm_3734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'comm_3734 ~v0 ~v1 v2 = du_'8853''45'comm_3734 v2
du_'8853''45'comm_3734 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'comm_3734 v0
  = coe
      du_'8853''45'comm_3560 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-cong
d_'8853''45'cong_3736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'cong_3736 ~v0 ~v1 v2 = du_'8853''45'cong_3736 v2
du_'8853''45'cong_3736 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'cong_3736 v0
  = coe
      du_'8853''45'cong_3546 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-identity
d_'8853''45'identity_3738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'identity_3738 ~v0 ~v1 v2
  = du_'8853''45'identity_3738 v2
du_'8853''45'identity_3738 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'identity_3738 v0
  = coe
      du_'8853''45'identity_3616 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-identityʳ
d_'8853''45'identity'691'_3740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8853''45'identity'691'_3740 ~v0 ~v1 v2
  = du_'8853''45'identity'691'_3740 v2
du_'8853''45'identity'691'_3740 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8853''45'identity'691'_3740 v0
  = coe
      du_'8853''45'identity'691'_3614 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-identityˡ
d_'8853''45'identity'737'_3742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8853''45'identity'737'_3742 ~v0 ~v1 v2
  = du_'8853''45'identity'737'_3742 v2
du_'8853''45'identity'737'_3742 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8853''45'identity'737'_3742 v0
  = coe
      du_'8853''45'identity'737'_3610 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-inverse
d_'8853''45'inverse_3744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'inverse_3744 ~v0 ~v1 v2 = du_'8853''45'inverse_3744 v2
du_'8853''45'inverse_3744 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'inverse_3744 v0
  = coe
      du_'8853''45'inverse_3624 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-inverseʳ
d_'8853''45'inverse'691'_3746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8853''45'inverse'691'_3746 ~v0 ~v1 v2
  = du_'8853''45'inverse'691'_3746 v2
du_'8853''45'inverse'691'_3746 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8853''45'inverse'691'_3746 v0
  = coe
      du_'8853''45'inverse'691'_3622 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-inverseˡ
d_'8853''45'inverse'737'_3748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8853''45'inverse'737'_3748 ~v0 ~v1 v2
  = du_'8853''45'inverse'737'_3748 v2
du_'8853''45'inverse'737'_3748 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8853''45'inverse'737'_3748 v0
  = coe
      du_'8853''45'inverse'737'_3618 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-isMagma
d_'8853''45'isMagma_3750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8853''45'isMagma_3750 ~v0 ~v1 v2 = du_'8853''45'isMagma_3750 v2
du_'8853''45'isMagma_3750 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8853''45'isMagma_3750 v0
  = coe
      du_'8853''45'isMagma_3692 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-isSemigroup
d_'8853''45'isSemigroup_3752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8853''45'isSemigroup_3752 ~v0 ~v1 v2
  = du_'8853''45'isSemigroup_3752 v2
du_'8853''45'isSemigroup_3752 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8853''45'isSemigroup_3752 v0
  = coe
      du_'8853''45'isSemigroup_3694 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-∧-commutativeRing
d_'8853''45''8743''45'commutativeRing_3754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4016
d_'8853''45''8743''45'commutativeRing_3754 ~v0 ~v1 v2
  = du_'8853''45''8743''45'commutativeRing_3754 v2
du_'8853''45''8743''45'commutativeRing_3754 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4016
du_'8853''45''8743''45'commutativeRing_3754 v0
  = coe
      du_'8853''45''8743''45'commutativeRing_3706 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-∧-isCommutativeRing
d_'8853''45''8743''45'isCommutativeRing_3756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796
d_'8853''45''8743''45'isCommutativeRing_3756 ~v0 ~v1 v2
  = du_'8853''45''8743''45'isCommutativeRing_3756 v2
du_'8853''45''8743''45'isCommutativeRing_3756 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796
du_'8853''45''8743''45'isCommutativeRing_3756 v0
  = coe
      du_'8853''45''8743''45'isCommutativeRing_3704 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-∧-isRing
d_'8853''45''8743''45'isRing_3758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_'8853''45''8743''45'isRing_3758 ~v0 ~v1 v2
  = du_'8853''45''8743''45'isRing_3758 v2
du_'8853''45''8743''45'isRing_3758 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
du_'8853''45''8743''45'isRing_3758 v0
  = coe
      du_'8853''45''8743''45'isRing_3702 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-⊥-isAbelianGroup
d_'8853''45''8869''45'isAbelianGroup_3760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'8853''45''8869''45'isAbelianGroup_3760 ~v0 ~v1 v2
  = du_'8853''45''8869''45'isAbelianGroup_3760 v2
du_'8853''45''8869''45'isAbelianGroup_3760 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
du_'8853''45''8869''45'isAbelianGroup_3760 v0
  = coe
      du_'8853''45''8869''45'isAbelianGroup_3700 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-⊥-isGroup
d_'8853''45''8869''45'isGroup_3762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_'8853''45''8869''45'isGroup_3762 ~v0 ~v1 v2
  = du_'8853''45''8869''45'isGroup_3762 v2
du_'8853''45''8869''45'isGroup_3762 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
du_'8853''45''8869''45'isGroup_3762 v0
  = coe
      du_'8853''45''8869''45'isGroup_3698 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-⊥-isMonoid
d_'8853''45''8869''45'isMonoid_3764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8853''45''8869''45'isMonoid_3764 ~v0 ~v1 v2
  = du_'8853''45''8869''45'isMonoid_3764 v2
du_'8853''45''8869''45'isMonoid_3764 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8853''45''8869''45'isMonoid_3764 v0
  = coe
      du_'8853''45''8869''45'isMonoid_3696 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 v1 v2)))))
