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

module MAlonzo.Code.Algebra.Lattice.Properties.BooleanAlgebra where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Consequences.Setoid
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice
import qualified MAlonzo.Code.Algebra.Lattice.Properties.Lattice
import qualified MAlonzo.Code.Algebra.Lattice.Properties.Semilattice
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Lattice.Bundles
import qualified MAlonzo.Code.Relation.Binary.Lattice.Structures
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Lattice.Properties.BooleanAlgebra._.IsAbelianGroup
d_IsAbelianGroup_116 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeMonoid
d_IsCommutativeMonoid_140 a0 a1 a2 a3 a4 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeRing
d_IsCommutativeRing_144 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeSemiring
d_IsCommutativeSemiring_152 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsGroup
d_IsGroup_164 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMagma
d_IsMagma_204 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMonoid
d_IsMonoid_216 a0 a1 a2 a3 a4 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing
d_IsRing_248 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemigroup
d_IsSemigroup_260 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemiring
d_IsSemiring_268 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsAbelianGroup.comm
d_comm_294 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_294 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_1186 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsAbelianGroup.isGroup
d_isGroup_316 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_316 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeMonoid.comm
d_comm_584 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_584 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_776 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeMonoid.isMonoid
d_isMonoid_600 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_600 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeRing.*-comm
d_'42''45'comm_630 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_630 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'comm_2906 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeRing.isRing
d_isRing_718 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_isRing_718 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeSemiring.*-comm
d_'42''45'comm_784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_784 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'comm_1766 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsCommutativeSemiring.isSemiring
d_isSemiring_854 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_854 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsGroup.inverse
d_inverse_992 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_992 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1090 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsGroup.isMonoid
d_isMonoid_1006 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1006 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_1028 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_1028 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1092 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMagma.isEquivalence
d_isEquivalence_1556 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1556 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMagma.∙-cong
d_'8729''45'cong_1570 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1570 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMonoid.identity
d_identity_1666 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1666 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_724 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsMonoid.isSemigroup
d_isSemigroup_1678 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1678 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.*-assoc
d_'42''45'assoc_2184 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_2184 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2766 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.*-cong
d_'42''45'cong_2186 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_2186 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'cong_2764 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.*-identity
d_'42''45'identity_2192 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2192 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2220 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2220 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsRing.distrib
d_distrib_2250 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2250 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2770 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemigroup.assoc
d_assoc_2412 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2412 v0
  = coe MAlonzo.Code.Algebra.Structures.d_assoc_498 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemigroup.isMagma
d_isMagma_2416 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2416 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2530 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2530 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsSemiring.zero
d_zero_2544 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2544 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1656 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._._DistributesOver_
d__DistributesOver__2740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__2740 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._._DistributesOverʳ_
d__DistributesOver'691'__2742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__2742 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._._DistributesOverˡ_
d__DistributesOver'737'__2744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__2744 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Associative
d_Associative_2760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Associative_2760 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Commutative
d_Commutative_2764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_2764 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Congruent₂
d_Congruent'8322'_2768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_2768 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Identity
d_Identity_2780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identity_2780 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Inverse
d_Inverse_2784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Inverse_2784 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Involutive
d_Involutive_2788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny) -> ()
d_Involutive_2788 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.LeftIdentity
d_LeftIdentity_2806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftIdentity_2806 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.LeftInverse
d_LeftInverse_2808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftInverse_2808 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.LeftZero
d_LeftZero_2814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftZero_2814 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.RightIdentity
d_RightIdentity_2836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightIdentity_2836 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.RightInverse
d_RightInverse_2838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightInverse_2838 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.RightZero
d_RightZero_2844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightZero_2844 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.Zero
d_Zero_2864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Zero_2864 = erased
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra
d_IsBooleanAlgebra_3006 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra.isDistributiveLattice
d_isDistributiveLattice_3034 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_isDistributiveLattice_3034 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra.¬-cong
d_'172''45'cong_3050 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'cong_3050 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra.∧-complement
d_'8743''45'complement_3058 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_3058 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3248
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.IsBooleanAlgebra.∨-complement
d_'8744''45'complement_3082 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_3082 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3246
      (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra._.poset
d_poset_3476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_3476 ~v0 ~v1 v2 = du_poset_3476 v2
du_poset_3476 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_3476 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_poset_162
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_306
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-idem
d_'8743''45'idem_3478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8743''45'idem_3478 ~v0 ~v1 v2 = du_'8743''45'idem_3478 v2
du_'8743''45'idem_3478 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8743''45'idem_3478 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_294
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isBand
d_'8743''45'isBand_3480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8743''45'isBand_3480 ~v0 ~v1 v2 = du_'8743''45'isBand_3480 v2
du_'8743''45'isBand_3480 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_'8743''45'isBand_3480 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isBand_302
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isMagma
d_'8743''45'isMagma_3482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8743''45'isMagma_3482 ~v0 ~v1 v2 = du_'8743''45'isMagma_3482 v2
du_'8743''45'isMagma_3482 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8743''45'isMagma_3482 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isMagma_298
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_3484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_3484 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_3484 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_3484 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_3484 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_306
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_3486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_'8743''45'isOrderTheoreticMeetSemilattice_3486 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_3486 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_3486 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_'8743''45'isOrderTheoreticMeetSemilattice_3486 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_306
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isSemigroup
d_'8743''45'isSemigroup_3488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8743''45'isSemigroup_3488 ~v0 ~v1 v2
  = du_'8743''45'isSemigroup_3488 v2
du_'8743''45'isSemigroup_3488 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8743''45'isSemigroup_3488 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isSemigroup_300
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isSemilattice
d_'8743''45'isSemilattice_3490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8743''45'isSemilattice_3490 ~v0 ~v1 v2
  = du_'8743''45'isSemilattice_3490 v2
du_'8743''45'isSemilattice_3490 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_'8743''45'isSemilattice_3490 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isSemilattice_304
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_3492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_3492 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_3492 v2
du_'8743''45'orderTheoreticJoinSemilattice_3492 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_3492 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_306
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_3494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
d_'8743''45'orderTheoreticMeetSemilattice_3494 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_3494 v2
du_'8743''45'orderTheoreticMeetSemilattice_3494 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
du_'8743''45'orderTheoreticMeetSemilattice_3494 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_306
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-semilattice
d_'8743''45'semilattice_3496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8743''45'semilattice_3496 ~v0 ~v1 v2
  = du_'8743''45'semilattice_3496 v2
du_'8743''45'semilattice_3496 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8743''45'semilattice_3496 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_306
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-∨-distributiveLattice
d_'8743''45''8744''45'distributiveLattice_3498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
d_'8743''45''8744''45'distributiveLattice_3498 ~v0 ~v1 v2
  = du_'8743''45''8744''45'distributiveLattice_3498 v2
du_'8743''45''8744''45'distributiveLattice_3498 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
du_'8743''45''8744''45'distributiveLattice_3498 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice.du_'8743''45''8744''45'distributiveLattice_744
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
         (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-∨-isDistributiveLattice
d_'8743''45''8744''45'isDistributiveLattice_3500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_'8743''45''8744''45'isDistributiveLattice_3500 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isDistributiveLattice_3500 v2
du_'8743''45''8744''45'isDistributiveLattice_3500 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
du_'8743''45''8744''45'isDistributiveLattice_3500 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice.du_'8743''45''8744''45'isDistributiveLattice_742
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
         (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-∨-isLattice
d_'8743''45''8744''45'isLattice_3502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8743''45''8744''45'isLattice_3502 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isLattice_3502 v2
du_'8743''45''8744''45'isLattice_3502 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
du_'8743''45''8744''45'isLattice_3502 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45''8744''45'isLattice_342
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-∨-lattice
d_'8743''45''8744''45'lattice_3504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8743''45''8744''45'lattice_3504 ~v0 ~v1 v2
  = du_'8743''45''8744''45'lattice_3504 v2
du_'8743''45''8744''45'lattice_3504 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
du_'8743''45''8744''45'lattice_3504 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45''8744''45'lattice_344
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-idem
d_'8744''45'idem_3506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8744''45'idem_3506 ~v0 ~v1 v2 = du_'8744''45'idem_3506 v2
du_'8744''45'idem_3506 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8744''45'idem_3506 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'idem_318
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-isBand
d_'8744''45'isBand_3508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8744''45'isBand_3508 ~v0 ~v1 v2 = du_'8744''45'isBand_3508 v2
du_'8744''45'isBand_3508 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_'8744''45'isBand_3508 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isBand_326
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-isMagma
d_'8744''45'isMagma_3510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8744''45'isMagma_3510 ~v0 ~v1 v2 = du_'8744''45'isMagma_3510 v2
du_'8744''45'isMagma_3510 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8744''45'isMagma_3510 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isMagma_322
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_3512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_3512 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_3512 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_3512 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_3512 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_330
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_3514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_'8743''45'isOrderTheoreticMeetSemilattice_3514 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_3514 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_3514 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_'8743''45'isOrderTheoreticMeetSemilattice_3514 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_330
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-isSemigroup
d_'8744''45'isSemigroup_3516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8744''45'isSemigroup_3516 ~v0 ~v1 v2
  = du_'8744''45'isSemigroup_3516 v2
du_'8744''45'isSemigroup_3516 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8744''45'isSemigroup_3516 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isSemigroup_324
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-isSemilattice
d_'8744''45'isSemilattice_3518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8744''45'isSemilattice_3518 ~v0 ~v1 v2
  = du_'8744''45'isSemilattice_3518 v2
du_'8744''45'isSemilattice_3518 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_'8744''45'isSemilattice_3518 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isSemilattice_328
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_3520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_3520 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_3520 v2
du_'8743''45'orderTheoreticJoinSemilattice_3520 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_3520 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_330
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_3522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
d_'8743''45'orderTheoreticMeetSemilattice_3522 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_3522 v2
du_'8743''45'orderTheoreticMeetSemilattice_3522 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
du_'8743''45'orderTheoreticMeetSemilattice_3522 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_330
               (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-semilattice
d_'8744''45'semilattice_3524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8744''45'semilattice_3524 ~v0 ~v1 v2
  = du_'8744''45'semilattice_3524 v2
du_'8744''45'semilattice_3524 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8744''45'semilattice_3524 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_330
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-∧-isOrderTheoreticLattice
d_'8744''45''8743''45'isOrderTheoreticLattice_3526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
d_'8744''45''8743''45'isOrderTheoreticLattice_3526 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isOrderTheoreticLattice_3526 v2
du_'8744''45''8743''45'isOrderTheoreticLattice_3526 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
du_'8744''45''8743''45'isOrderTheoreticLattice_3526 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45''8743''45'isOrderTheoreticLattice_356
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.∨-∧-orderTheoreticLattice
d_'8744''45''8743''45'orderTheoreticLattice_3528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_394
d_'8744''45''8743''45'orderTheoreticLattice_3528 ~v0 ~v1 v2
  = du_'8744''45''8743''45'orderTheoreticLattice_3528 v2
du_'8744''45''8743''45'orderTheoreticLattice_3528 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_394
du_'8744''45''8743''45'orderTheoreticLattice_3528 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45''8743''45'orderTheoreticLattice_412
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678 (coe v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-isBooleanAlgebra
d_'8743''45''8744''45'isBooleanAlgebra_3530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224
d_'8743''45''8744''45'isBooleanAlgebra_3530 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isBooleanAlgebra_3530 v2
du_'8743''45''8744''45'isBooleanAlgebra_3530 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224
du_'8743''45''8744''45'isBooleanAlgebra_3530 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3314
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice.du_'8743''45''8744''45'isDistributiveLattice_742
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3248
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3246
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
            (coe v0)))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-booleanAlgebra
d_'8743''45''8744''45'booleanAlgebra_3532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698
d_'8743''45''8744''45'booleanAlgebra_3532 ~v0 ~v1 v2
  = du_'8743''45''8744''45'booleanAlgebra_3532 v2
du_'8743''45''8744''45'booleanAlgebra_3532 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698
du_'8743''45''8744''45'booleanAlgebra_3532 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_822
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe du_'8743''45''8744''45'isBooleanAlgebra_3530 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-identityʳ
d_'8743''45'identity'691'_3534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8743''45'identity'691'_3534 ~v0 ~v1 v2 v3
  = du_'8743''45'identity'691'_3534 v2 v3
du_'8743''45'identity'691'_3534 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8743''45'identity'691'_3534 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
            v1 v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe v1))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3122
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3308
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))
                  v1))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-identityˡ
d_'8743''45'identity'737'_3538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8743''45'identity'737'_3538 ~v0 ~v1 v2
  = du_'8743''45'identity'737'_3538 v2
du_'8743''45'identity'737'_3538 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8743''45'identity'737'_3538 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'id'691''8658'id'737'_366
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_586
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
               (coe v0))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe du_'8743''45'identity'691'_3534 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-identity
d_'8743''45'identity_3540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'identity_3540 ~v0 ~v1 v2
  = du_'8743''45'identity_3540 v2
du_'8743''45'identity_3540 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'identity_3540 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8743''45'identity'737'_3538 (coe v0))
      (coe du_'8743''45'identity'691'_3534 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-identityʳ
d_'8744''45'identity'691'_3542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8744''45'identity'691'_3542 ~v0 ~v1 v2 v3
  = du_'8744''45'identity'691'_3542 v2 v3
du_'8744''45'identity'691'_3542 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8744''45'identity'691'_3542 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
            v1 v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe v1))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3120
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))
                  v1))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-identityˡ
d_'8744''45'identity'737'_3546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8744''45'identity'737'_3546 ~v0 ~v1 v2
  = du_'8744''45'identity'737'_3546 v2
du_'8744''45'identity'737'_3546 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8744''45'identity'737'_3546 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'id'691''8658'id'737'_366
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_586
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
               (coe v0))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe du_'8744''45'identity'691'_3542 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-identity
d_'8744''45'identity_3548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'identity_3548 ~v0 ~v1 v2
  = du_'8744''45'identity_3548 v2
du_'8744''45'identity_3548 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8744''45'identity_3548 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8744''45'identity'737'_3546 (coe v0))
      (coe du_'8744''45'identity'691'_3542 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-zeroʳ
d_'8743''45'zero'691'_3550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8743''45'zero'691'_3550 ~v0 ~v1 v2 v3
  = du_'8743''45'zero'691'_3550 v2 v3
du_'8743''45'zero'691'_3550 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8743''45'zero'691'_3550 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))
                     v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v1)
                  (coe v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_294
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
                           (coe v0)))
                     (coe v1))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               v1 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0))
               v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-zeroˡ
d_'8743''45'zero'737'_3554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8743''45'zero'737'_3554 ~v0 ~v1 v2
  = du_'8743''45'zero'737'_3554 v2
du_'8743''45'zero'737'_3554 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8743''45'zero'737'_3554 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'691''8658'ze'737'_386
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_586
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
               (coe v0))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe du_'8743''45'zero'691'_3550 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-zero
d_'8743''45'zero_3556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'zero_3556 ~v0 ~v1 v2 = du_'8743''45'zero_3556 v2
du_'8743''45'zero_3556 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'zero_3556 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8743''45'zero'737'_3554 (coe v0))
      (coe du_'8743''45'zero'691'_3550 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-zeroʳ
d_'8744''45'zero'691'_3560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8744''45'zero'691'_3560 ~v0 ~v1 v2 v3
  = du_'8744''45'zero'691'_3560 v2 v3
du_'8744''45'zero'691'_3560 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8744''45'zero'691'_3560 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3308
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))
                     v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v1)
                  (coe v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'idem_318
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
                           (coe v0)))
                     (coe v1))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               v1 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3308
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0))
               v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-zeroˡ
d_'8744''45'zero'737'_3564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8744''45'zero'737'_3564 ~v0 ~v1 v2
  = du_'8744''45'zero'737'_3564 v2
du_'8744''45'zero'737'_3564 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8744''45'zero'737'_3564 v0
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'691''8658'ze'737'_386
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_586
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
               (coe v0))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe du_'8744''45'zero'691'_3560 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-zero
d_'8744''45'zero_3566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'zero_3566 ~v0 ~v1 v2 = du_'8744''45'zero_3566 v2
du_'8744''45'zero_3566 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8744''45'zero_3566 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8744''45'zero'737'_3564 (coe v0))
      (coe du_'8744''45'zero'691'_3560 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-⊥-isMonoid
d_'8744''45''8869''45'isMonoid_3568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8744''45''8869''45'isMonoid_3568 ~v0 ~v1 v2
  = du_'8744''45''8869''45'isMonoid_3568 v2
du_'8744''45''8869''45'isMonoid_3568 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8744''45''8869''45'isMonoid_3568 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isSemigroup_324
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
               (coe v0))))
      (coe du_'8744''45'identity_3548 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-⊤-isMonoid
d_'8743''45''8868''45'isMonoid_3570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8743''45''8868''45'isMonoid_3570 ~v0 ~v1 v2
  = du_'8743''45''8868''45'isMonoid_3570 v2
du_'8743''45''8868''45'isMonoid_3570 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8743''45''8868''45'isMonoid_3570 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isSemigroup_300
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
               (coe v0))))
      (coe du_'8743''45'identity_3540 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-⊥-isCommutativeMonoid
d_'8744''45''8869''45'isCommutativeMonoid_3572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'8744''45''8869''45'isCommutativeMonoid_3572 ~v0 ~v1 v2
  = du_'8744''45''8869''45'isCommutativeMonoid_3572 v2
du_'8744''45''8869''45'isCommutativeMonoid_3572 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'8744''45''8869''45'isCommutativeMonoid_3572 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe du_'8744''45''8869''45'isMonoid_3568 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-⊤-isCommutativeMonoid
d_'8743''45''8868''45'isCommutativeMonoid_3574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'8743''45''8868''45'isCommutativeMonoid_3574 ~v0 ~v1 v2
  = du_'8743''45''8868''45'isCommutativeMonoid_3574 v2
du_'8743''45''8868''45'isCommutativeMonoid_3574 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'8743''45''8868''45'isCommutativeMonoid_3574 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe du_'8743''45''8868''45'isMonoid_3570 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-∧-isSemiring
d_'8744''45''8743''45'isSemiring_3576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_'8744''45''8743''45'isSemiring_3576 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isSemiring_3576 v2
du_'8744''45''8743''45'isSemiring_3576 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
du_'8744''45''8743''45'isSemiring_3576 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1740
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1630
         (coe du_'8744''45''8869''45'isCommutativeMonoid_3572 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0)))))
         (coe du_'8743''45'identity_3540 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3162
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe du_'8743''45'zero_3556 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-isSemiring
d_'8743''45''8744''45'isSemiring_3578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_'8743''45''8744''45'isSemiring_3578 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isSemiring_3578 v2
du_'8743''45''8744''45'isSemiring_3578 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
du_'8743''45''8744''45'isSemiring_3578 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1740
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1630
         (coe du_'8743''45''8868''45'isCommutativeMonoid_3574 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0)))))
         (coe du_'8744''45'identity_3548 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3160
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe du_'8744''45'zero_3566 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-∧-isCommutativeSemiring
d_'8744''45''8743''45'isCommutativeSemiring_3580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_'8744''45''8743''45'isCommutativeSemiring_3580 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isCommutativeSemiring_3580 v2
du_'8744''45''8743''45'isCommutativeSemiring_3580 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
du_'8744''45''8743''45'isCommutativeSemiring_3580 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe du_'8744''45''8743''45'isSemiring_3576 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-isCommutativeSemiring
d_'8743''45''8744''45'isCommutativeSemiring_3582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_'8743''45''8744''45'isCommutativeSemiring_3582 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isCommutativeSemiring_3582 v2
du_'8743''45''8744''45'isCommutativeSemiring_3582 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
du_'8743''45''8744''45'isCommutativeSemiring_3582 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe du_'8743''45''8744''45'isSemiring_3578 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.∨-∧-commutativeSemiring
d_'8744''45''8743''45'commutativeSemiring_3584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
d_'8744''45''8743''45'commutativeSemiring_3584 ~v0 ~v1 v2
  = du_'8744''45''8743''45'commutativeSemiring_3584 v2
du_'8744''45''8743''45'commutativeSemiring_3584 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
du_'8744''45''8743''45'commutativeSemiring_3584 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2706
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe du_'8744''45''8743''45'isCommutativeSemiring_3580 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.∧-∨-commutativeSemiring
d_'8743''45''8744''45'commutativeSemiring_3586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
d_'8743''45''8744''45'commutativeSemiring_3586 ~v0 ~v1 v2
  = du_'8743''45''8744''45'commutativeSemiring_3586 v2
du_'8743''45''8744''45'commutativeSemiring_3586 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
du_'8743''45''8744''45'commutativeSemiring_3586 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2706
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe du_'8743''45''8744''45'isCommutativeSemiring_3582 (coe v0))
-- Algebra.Lattice.Properties.BooleanAlgebra.lemma
d_lemma_3592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma_3592 ~v0 ~v1 v2 v3 v4 v5 v6 = du_lemma_3592 v2 v3 v4 v5 v6
du_lemma_3592 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma_3592 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
               v2
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                  v2
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                     v2
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                           v2)
                        v2
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                             (coe v0)))))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                              v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)) v2)
                           v2
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                (coe v0)))))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)) v2)
                              v2 v2
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                   (coe v0)))))))
                                 (coe v2))
                              (coe du_'8743''45'identity'737'_3538 v0 v2))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0))))
                              (coe v2)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3308
                                 (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))
                                 v1)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3210
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))
                           v2 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'737'_3310
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))
                        v1)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3208
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0)))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1
                  v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
               (coe v4)))
         (coe
            du_'8743''45'identity'691'_3534 (coe v0)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
-- Algebra.Lattice.Properties.BooleanAlgebra.¬⊥≈⊤
d_'172''8869''8776''8868'_3602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny
d_'172''8869''8776''8868'_3602 ~v0 ~v1 v2
  = du_'172''8869''8776''8868'_3602 v2
du_'172''8869''8776''8868'_3602 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny
du_'172''8869''8776''8868'_3602 v0
  = coe
      du_lemma_3592 (coe v0)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe
         du_'8743''45'identity'691'_3534 (coe v0)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
      (coe
         du_'8744''45'zero'691'_3560 (coe v0)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
-- Algebra.Lattice.Properties.BooleanAlgebra.¬⊤≈⊥
d_'172''8868''8776''8869'_3604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny
d_'172''8868''8776''8869'_3604 ~v0 ~v1 v2
  = du_'172''8868''8776''8869'_3604 v2
du_'172''8868''8776''8869'_3604 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny
du_'172''8868''8776''8869'_3604 v0
  = coe
      du_lemma_3592 (coe v0)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe
         du_'8743''45'zero'691'_3550 (coe v0)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
      (coe
         du_'8744''45'identity'691'_3542 (coe v0)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
-- Algebra.Lattice.Properties.BooleanAlgebra.¬-involutive
d_'172''45'involutive_3606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'172''45'involutive_3606 ~v0 ~v1 v2 v3
  = du_'172''45'involutive_3606 v2 v3
du_'172''45'involutive_3606 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'172''45'involutive_3606 v0 v1
  = coe
      du_lemma_3592 (coe v0)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
      (coe v1)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'737'_3310
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
            (coe v0))
         v1)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3306
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
            (coe v0))
         v1)
-- Algebra.Lattice.Properties.BooleanAlgebra.deMorgan₁
d_deMorgan'8321'_3614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_deMorgan'8321'_3614 ~v0 ~v1 v2 v3 v4
  = du_deMorgan'8321'_3614 v2 v3 v4
du_deMorgan'8321'_3614 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_deMorgan'8321'_3614 v0 v1 v2
  = coe
      du_lemma_3592 (coe v0)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
      (coe du_lem'8321'_3624 (coe v0) (coe v1) (coe v2))
      (coe du_lem'8322'_3628 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra._.lem₁
d_lem'8321'_3624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lem'8321'_3624 ~v0 ~v1 v2 v3 v4 = du_lem'8321'_3624 v2 v3 v4
du_lem'8321'_3624 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8321'_3624 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                             (coe v0)))))))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                        (coe
                           du_'8744''45'identity'691'_3542 (coe v0)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe du_'8743''45'zero'691'_3550 (coe v0) (coe v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                        (coe du_'8743''45'zero'691'_3550 (coe v0) (coe v1))))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))
                           v1))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2)
                           (\ v3 v4 -> v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v3 v4 -> v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1)
                           (\ v3 v4 -> v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v3 v4 -> v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))
                           v2))))
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v2 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v1 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (\ v3 ->
                     coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (\ v3 v4 -> v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v3 v4 -> v4)
                  (\ v3 ->
                     coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v1 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3208
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
-- Algebra.Lattice.Properties.BooleanAlgebra._.lem₃
d_lem'8323'_3626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lem'8323'_3626 ~v0 ~v1 v2 v3 v4 = du_lem'8323'_3626 v2 v3 v4
du_lem'8323'_3626 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8323'_3626 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v2 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
               (coe
                  du_'8743''45'identity'737'_3538 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3308
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))
                  v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3206
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1
            v2))
-- Algebra.Lattice.Properties.BooleanAlgebra._.lem₂
d_lem'8322'_3628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322'_3628 ~v0 ~v1 v2 v3 v4 = du_lem'8322'_3628 v2 v3 v4
du_lem'8322'_3628 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322'_3628 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
                     (coe
                        du_'8744''45'zero'691'_3560 (coe v0)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3308
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))
                        v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe du_lem'8323'_3626 (coe v0) (coe v1) (coe v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
-- Algebra.Lattice.Properties.BooleanAlgebra.deMorgan₂
d_deMorgan'8322'_3634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_deMorgan'8322'_3634 ~v0 ~v1 v2 v3 v4
  = du_deMorgan'8322'_3634 v2 v3 v4
du_deMorgan'8322'_3634 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_deMorgan'8322'_3634 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  du_'172''45'involutive_3606 (coe v0)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  du_deMorgan'8321'_3614 (coe v0)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe du_'172''45'involutive_3606 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  v2)
               (coe du_'172''45'involutive_3606 (coe v0) (coe v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._⊕_
d__'8853'__3650 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d__'8853'__3650 ~v0 v1 ~v2 = du__'8853'__3650 v1
du__'8853'__3650 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'8853'__3650 v0 = coe v0
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.helper
d_helper_3660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_helper_3660 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_helper_3660 v2 v5 v6 v7 v8 v9 v10
du_helper_3660 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_helper_3660 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240 (coe v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
         (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0))))
         v1 v2
         (coe
            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
            (\ v7 v8 -> v7) v3 v4)
         (coe
            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
            (\ v7 v8 -> v8)
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0)) v3
            v4))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
            (coe v0))
         v3 v4 v6)
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-cong
d_'8853''45'cong_3666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'cong_3666 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_'8853''45'cong_3666 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_'8853''45'cong_3666 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'cong_3666 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v9 v10 v11 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v11)
      (coe v1 v3 v5) (coe v1 v4 v6)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe v1 v3 v5)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v5)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5)))
         (coe v1 v4 v6)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v6)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v6)))
            (coe v1 v4 v6)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v6)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v6)))
               (coe v1 v4 v6) (coe v1 v4 v6)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe v1 v4 v6))
               (coe v2 v4 v6))
            (coe
               du_helper_3660 (coe v0)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v5)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v6)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v6)
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240 (coe v7)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v3 v4 v5 v6)
                  (coe v8))
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240 (coe v7)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v3 v4 v5 v6)
                  (coe v8))))
         (coe v2 v3 v5))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-comm
d_'8853''45'comm_3680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'comm_3680 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'8853''45'comm_3680 v2 v3 v4 v5 v6
du_'8853''45'comm_3680 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'comm_3680 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe v1 v3 v4) (coe v1 v4 v3)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe v1 v3 v4)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
         (coe v1 v4 v3)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))
            (coe v1 v4 v3)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))
               (coe v1 v4 v3) (coe v1 v4 v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe v1 v4 v3))
               (coe v2 v4 v3))
            (coe
               du_helper_3660 (coe v0)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  v3 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  v3 v4)))
         (coe v2 v3 v4))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.¬-distribˡ-⊕
d_'172''45'distrib'737''45''8853'_3690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'distrib'737''45''8853'_3690 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'172''45'distrib'737''45''8853'_3690 v2 v3 v4 v5 v6
du_'172''45'distrib'737''45''8853'_3690 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'172''45'distrib'737''45''8853'_3690 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
         (coe v1 v3 v4))
      (coe
         v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
         v4)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe v1 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4))))
         (coe
            v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
            v4)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))))
            (coe
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
               v4)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                  v4)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                  (coe
                     v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                     v4)
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                     (coe
                        v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                        v4)
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                        (coe
                           v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                           v4)
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                             (coe v0)))))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3) v4)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    v4)))
                           (coe
                              v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                              v4)
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                (coe v0)))))))
                              (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                             (coe v0))))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    v4)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       v4)))
                              (coe
                                 v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 v4)
                              (coe
                                 v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 v4)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                   (coe v0)))))))
                                 (coe
                                    v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    v4))
                              (coe
                                 v2 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 v4))
                           (coe
                              du_helper_3660 (coe v0)
                              (coe
                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                                 (\ v5 v6 -> v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 v4)
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v5 v6 -> v6)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 v4)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3) v4)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0))))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 (coe v4) (coe du_'172''45'involutive_3606 (coe v0) (coe v4)))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                                 (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0))))
                                 v4 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)))
                           (coe
                              du_deMorgan'8321'_3614 (coe v0) (coe v3)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))))
                     (coe
                        du_deMorgan'8322'_3634 (coe v0)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe du_lem_3704 (coe v0) (coe v3) (coe v4))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                        (coe du_lem_3704 (coe v0) (coe v4) (coe v3)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4))))
                     (\ v5 v6 -> v5)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4)
                        (\ v5 v6 -> v5)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v5 v6 -> v6)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v5 v6 -> v6)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4))))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4)
                        (\ v5 v6 -> v5)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v5 v6 -> v6)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4)
                        (\ v5 v6 -> v5)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v5 v6 -> v6)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe v4)
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (\ v5 v6 -> v5)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0))))
                              v3 v4))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3210
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4))
                  v3 v4)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
               (coe v0))
            (coe v1 v3 v4)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)))
            (coe v2 v3 v4)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem
d_lem_3704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem_3704 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 = du_lem_3704 v2 v7 v8
du_lem_3704 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem_3704 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                  (coe
                     du_'8744''45'identity'737'_3546 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))
                     v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3208
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0)))
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe du_deMorgan'8321'_3614 (coe v0) (coe v1) (coe v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.¬-distribʳ-⊕
d_'172''45'distrib'691''45''8853'_3714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'distrib'691''45''8853'_3714 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'172''45'distrib'691''45''8853'_3714 v2 v3 v4 v5 v6
du_'172''45'distrib'691''45''8853'_3714 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'172''45'distrib'691''45''8853'_3714 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
         (coe v1 v3 v4))
      (coe
         v1 v3
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe v1 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe v1 v4 v3))
         (coe
            v1 v3
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe v1 v4 v3))
            (coe
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
               v3)
            (coe
               v1 v3
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                  v3)
               (coe
                  v1 v3
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
               (coe
                  v1 v3
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     v1 v3
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)))
               (coe
                  du_'8853''45'comm_3680 (coe v0) (coe v1) (coe v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                  (coe v3)))
            (coe
               du_'172''45'distrib'737''45''8853'_3690 (coe v0) (coe v1) (coe v2)
               (coe v4) (coe v3)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
               (coe v0))
            (coe v1 v3 v4) (coe v1 v4 v3)
            (coe
               du_'8853''45'comm_3680 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-annihilates-¬
d_'8853''45'annihilates'45''172'_3724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'annihilates'45''172'_3724 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'8853''45'annihilates'45''172'_3724 v2 v3 v4 v5 v6
du_'8853''45'annihilates'45''172'_3724 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'annihilates'45''172'_3724 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe v1 v3 v4)
      (coe
         v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe v1 v3 v4)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe v1 v3 v4)))
         (coe
            v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe v1 v3 v4)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                  v4))
            (coe
               v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                     v4))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)))
               (coe
                  du_'172''45'distrib'691''45''8853'_3714 (coe v0) (coe v1) (coe v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                  (coe v4)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe v1 v3 v4))
               (coe
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                  v4)
               (coe
                  du_'172''45'distrib'737''45''8853'_3690 (coe v0) (coe v1) (coe v2)
                  (coe v3) (coe v4))))
         (coe du_'172''45'involutive_3606 (coe v0) (coe v1 v3 v4)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-identityˡ
d_'8853''45'identity'737'_3730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8853''45'identity'737'_3730 ~v0 ~v1 v2 v3 v4 v5
  = du_'8853''45'identity'737'_3730 v2 v3 v4 v5
du_'8853''45'identity'737'_3730 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8853''45'identity'737'_3730 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         v1 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)
      v3
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            v1 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)))
         v3
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))))
            v3
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
               v3
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
                  v3 v3
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe v3))
                  (coe du_'8743''45'identity'691'_3534 (coe v0) (coe v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (coe du_'172''8869''8776''8868'_3602 (coe v0))))
            (coe
               du_helper_3660 (coe v0)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)
               (coe v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
               (coe du_'8744''45'identity'737'_3546 v0 v3)
               (coe du_'8743''45'zero'737'_3554 v0 v3)))
         (coe
            v2 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
            v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-identityʳ
d_'8853''45'identity'691'_3734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8853''45'identity'691'_3734 ~v0 ~v1 v2 v3 v4 v5
  = du_'8853''45'identity'691'_3734 v2 v3 v4 v5
du_'8853''45'identity'691'_3734 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8853''45'identity'691'_3734 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
      (coe
         du_'8853''45'comm_3680 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0)))))
         (coe
            v1 v3 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
         (coe
            v1 (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)) v3)
         v3)
      (coe
         du_'8853''45'identity'737'_3730 (coe v0) (coe v1) (coe v2)
         (coe v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-identity
d_'8853''45'identity_3736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'identity_3736 ~v0 ~v1 v2 v3 v4
  = du_'8853''45'identity_3736 v2 v3 v4
du_'8853''45'identity_3736 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'identity_3736 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8853''45'identity'737'_3730 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'identity'691'_3734 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-inverseˡ
d_'8853''45'inverse'737'_3738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8853''45'inverse'737'_3738 ~v0 ~v1 v2 v3 v4 v5
  = du_'8853''45'inverse'737'_3738 v2 v3 v4 v5
du_'8853''45'inverse'737'_3738 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8853''45'inverse'737'_3738 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe v1 v3 v3)
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe v1 v3 v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v3)))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))
                  v3))
            (coe
               du_helper_3660 (coe v0)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v3)
               (coe v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v3)
               (coe v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'idem_318
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
                        (coe v0)))
                  (coe v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_294
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
                        (coe v0)))
                  (coe v3))))
         (coe v2 v3 v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-inverseʳ
d_'8853''45'inverse'691'_3742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8853''45'inverse'691'_3742 ~v0 ~v1 v2 v3 v4 v5
  = du_'8853''45'inverse'691'_3742 v2 v3 v4 v5
du_'8853''45'inverse'691'_3742 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'8853''45'inverse'691'_3742 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
      (coe
         du_'8853''45'comm_3680 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0)))))
         (coe v1 v3 v3) (coe v1 v3 v3)
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
      (coe
         du_'8853''45'inverse'737'_3738 (coe v0) (coe v1) (coe v2) (coe v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-inverse
d_'8853''45'inverse_3744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'inverse_3744 ~v0 ~v1 v2 v3 v4
  = du_'8853''45'inverse_3744 v2 v3 v4
du_'8853''45'inverse_3744 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'inverse_3744 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'8853''45'inverse'737'_3738 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'inverse'691'_3742 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.∧-distribˡ-⊕
d_'8743''45'distrib'737''45''8853'_3746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8853'_3746 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8743''45'distrib'737''45''8853'_3746 v2 v3 v4 v5 v6 v7
du_'8743''45'distrib'737''45''8853'_3746 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8853'_3746 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v6 v7 v8 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
         (coe v1 v4 v5))
      (coe
         v1
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
            (coe v1 v4 v5))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))
         (coe
            v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5)))
            (coe
               v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
               (coe
                  v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                  (coe
                     v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                     (coe
                        v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                        (coe
                           v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                             (coe v0)))))))
                           (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0))))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                       v5))))
                           (coe
                              v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                (coe v0)))))))
                              (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                             (coe v0))))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                          v5))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                          v5))))
                              (coe
                                 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v5))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                   (coe v0)))))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v4 v5))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v5))))
                                 (coe
                                    v1
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                       v5))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                      (coe v0)))))))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             v4 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v5))))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v5))))
                                    (coe
                                       v1
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                          v5))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                      (coe
                                                         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                         (coe v0)))))))
                                       (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                      (coe v0))))))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v5))
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                   v0 v3 v4)
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                   v0 v3 v5))))
                                       (coe
                                          v1
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v5))
                                       (coe
                                          v1
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v5))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                                      (coe
                                                         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                         (coe
                                                            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                            (coe v0)))))))
                                          (coe
                                             v1
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v5)))
                                       (coe
                                          v2
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v5)))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                (coe v0))))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v5)))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             v4 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v5))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3208
                                          (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                (coe v0)))
                                          v3 v4 v5)))
                                 (coe
                                    du_helper_3660 (coe v0)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                          v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                          v5))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                       (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                   (coe v0)))))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             v4 v5)))
                                    (coe du_lem'8321'_3760 (coe v0) (coe v3) (coe v4) (coe v5))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                          v5)))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                          v5)))
                                 (coe
                                    du_deMorgan'8321'_3614 (coe v0) (coe v3)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                       v5))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                              (coe
                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                                 (\ v6 v7 -> v6)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v6 v7 -> v7)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0))))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                                 (coe du_deMorgan'8321'_3614 (coe v0) (coe v4) (coe v5)))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3208
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                        (coe du_lem'8323'_3762 (coe v0) (coe v3) (coe v4) (coe v5))))
                  (coe
                     du_'8744''45'identity'737'_3546 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                  (coe du_deMorgan'8321'_3614 (coe v0) (coe v4) (coe v5))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               v3
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe v3) (coe v1 v4 v5)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5)))
            (coe v2 v4 v5)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₂
d_lem'8322'_3758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322'_3758 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8322'_3758 v2 v5 v6 v7
du_lem'8322'_3758 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322'_3758 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  v2 v1 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v1)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  v1 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            v1 v2 v3))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₁
d_lem'8321'_3760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8321'_3760 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8321'_3760 v2 v5 v6 v7
du_lem'8321'_3760 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8321'_3760 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v1 v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v3))
                  (coe du_lem'8322'_3758 (coe v0) (coe v1) (coe v2) (coe v3))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               v1 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v1)
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_294
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
                     (coe v0)))
               (coe v1))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₃
d_lem'8323'_3762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8323'_3762 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8323'_3762 v2 v5 v6 v7
du_lem'8323'_3762 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8323'_3762 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
            (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                     v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                        v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                        v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                        v1)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                  v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))
                  v1)))
         (coe
            du_'8743''45'zero'691'_3550 (coe v0)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.∧-distribʳ-⊕
d_'8743''45'distrib'691''45''8853'_3764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8853'_3764 ~v0 ~v1 v2 v3 v4
  = du_'8743''45'distrib'691''45''8853'_3764 v2 v3 v4
du_'8743''45'distrib'691''45''8853'_3764 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8853'_3764 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'737''8658'distr'691'_536
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_586
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_678
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_806
               (coe v0))))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 (coe v0))
      (coe v1) (coe du_'8853''45'cong_3666 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe
         du_'8743''45'distrib'737''45''8853'_3746 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.∧-distrib-⊕
d_'8743''45'distrib'45''8853'_3766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8853'_3766 ~v0 ~v1 v2 v3 v4
  = du_'8743''45'distrib'45''8853'_3766 v2 v3 v4
du_'8743''45'distrib'45''8853'_3766 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'distrib'45''8853'_3766 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8743''45'distrib'737''45''8853'_3746 (coe v0) (coe v1)
         (coe v2))
      (coe
         du_'8743''45'distrib'691''45''8853'_3764 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.lemma₂
d_lemma'8322'_3776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lemma'8322'_3776 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_lemma'8322'_3776 v2 v5 v6 v7 v8
du_lemma'8322'_3776 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lemma'8322'_3776 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v3)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v4)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v4)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
               v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v3)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v4)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                  v4))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v4)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v3)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v4)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v3)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v4)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v4))))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3206
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0)))
                  v3 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v3)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                     v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v4)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v4)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3206
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0)))
                  v4 v1 v2)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3204
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
            v3 v4))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-assoc
d_'8853''45'assoc_3786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'assoc_3786 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8853''45'assoc_3786 v2 v3 v4 v5 v6 v7
du_'8853''45'assoc_3786 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'assoc_3786 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe v1 v3 (coe v1 v4 v5)) (coe v1 (coe v1 v3 v4) v5)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v6 v7 v8 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v8)
         (coe v1 v3 (coe v1 v4 v5)) (coe v1 (coe v1 v3 v4) v5)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe v1 v3 (coe v1 v4 v5))
            (coe
               v1 v3
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))
            (coe v1 (coe v1 v3 v4) v5)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  v1 v3
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))))
               (coe v1 (coe v1 v3 v4) v5)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                    v5))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3) v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                  (coe v1 (coe v1 v3 v4) v5)
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3) v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    v4)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))))
                     (coe v1 (coe v1 v3 v4) v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       v4)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       v4)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))))
                        (coe v1 (coe v1 v3 v4) v5)
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                             (coe v0)))))))
                           (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0))))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v4))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v3)
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          v5)))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                    v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                           (coe v1 (coe v1 v3 v4) v5)
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                (coe v0)))))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          v4)
                                       v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v3)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v4))
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v4))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v3)
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          v5))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)))
                                       v5)))
                              (coe v1 (coe v1 v3 v4) v5)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                   (coe v0)))))))
                                 (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                (coe v0))))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)))
                                       v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724
                                                v0 v3 v4)
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                   v0 v3 v4)))
                                          v5)))
                                 (coe
                                    v1
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)))
                                    v5)
                                 (coe v1 (coe v1 v3 v4) v5)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                      (coe v0)))))))
                                    (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                   (coe v0))))))
                                    (coe
                                       v1
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)))
                                       v5)
                                    (coe v1 (coe v1 v3 v4) v5) (coe v1 (coe v1 v3 v4) v5)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                      (coe
                                                         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                         (coe v0)))))))
                                       (coe v1 (coe v1 v3 v4) v5))
                                    (coe
                                       du_'8853''45'cong_3666 (coe v0) (coe v1) (coe v2)
                                       (coe v1 v3 v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)))
                                       (coe v5) (coe v5) (coe v2 v3 v4)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                          (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                                (coe
                                                   MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                                   (coe
                                                      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                                      (coe v0)))))
                                          v5)))
                                 (coe
                                    v2
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)))
                                    v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                                 (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0))))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          v4)
                                       v5)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v3)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v4))
                                       v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                             v3 v4)))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v4))
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             v3)
                                          v4)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                             v3 v4)
                                          (coe
                                             MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                             (coe
                                                MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726
                                                v0 v3 v4)))
                                       v5))
                                 (coe du_lem'8321'_3798 (coe v0) (coe v3) (coe v4) (coe v5))
                                 (coe du_lem'8322'_3802 (coe v0) (coe v3) (coe v4) (coe v5))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
                              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0))))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       v4)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                    v5)
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                       (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                       v4)
                                    (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))))
                           (coe du_lem'8325'_3810 (coe v0) (coe v3) (coe v4) (coe v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                              v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3) v4)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3 v4)
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v3
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v3
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4
                                    v5)))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v4))
                           v5)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3) v4)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v5)))
                     (coe du_lem'8323'_3804 (coe v0) (coe v3) (coe v4) (coe v5))
                     (coe du_lem'8324'_3808 (coe v0) (coe v3) (coe v4) (coe v5))))
               (coe
                  v2 v3
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5)))))
            (coe
               du_'8853''45'cong_3666 (coe v0) (coe v1) (coe v2) (coe v3) (coe v3)
               (coe v1 v4 v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v4 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v4 v5)))
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))
                  v3)
               (coe v2 v4 v5))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₁
d_lem'8321'_3798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8321'_3798 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8321'_3798 v2 v5 v6 v7
du_lem'8321'_3798 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8321'_3798 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            v3))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
         v3)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
            v3)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
               v3)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
                  v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe v3)
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
                  (\ v4 v5 -> v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe du_deMorgan'8321'_3614 (coe v0) (coe v1) (coe v2)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3206
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))
            v3
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₂′
d_lem'8322''8242'_3800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322''8242'_3800 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 ~v7
  = du_lem'8322''8242'_3800 v2 v5 v6
du_lem'8322''8242'_3800 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322''8242'_3800 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
                                    v2)))))
                     (coe
                        du_deMorgan'8321'_3614 (coe v0)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)
                     (coe du_deMorgan'8322'_3634 (coe v0) (coe v1) (coe v2))
                     (coe
                        du_'172''45'involutive_3606 (coe v0)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
               (coe
                  du_lemma'8322'_3776 (coe v0)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                  (coe v1) (coe v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                  (\ v3 v4 -> v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v3 v4 -> v4)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                  (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3306
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))
                     v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3306
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))
                     v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
            (coe
               du_'8743''45'identity'737'_3538 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
            (coe
               du_'8743''45'identity'691'_3534 (coe v0)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₂
d_lem'8322'_3802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8322'_3802 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8322'_3802 v2 v5 v6 v7
du_lem'8322'_3802 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8322'_3802 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
            v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
               v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
                  v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
                     v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
                     v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
                        v3)))
               (coe
                  du_deMorgan'8321'_3614 (coe v0)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
                  (coe v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
               (coe du_lem'8322''8242'_3800 (coe v0) (coe v1) (coe v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3206
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₃
d_lem'8323'_3804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8323'_3804 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8323'_3804 v2 v5 v6 v7
du_lem'8323'_3804 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8323'_3804 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
               (coe
                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v1 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
                     (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))))
                     v1 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3204
               (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0)))
               v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe v1)
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
               (\ v4 v5 -> v4)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
               (coe du_deMorgan'8321'_3614 (coe v0) (coe v2) (coe v3)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₄′
d_lem'8324''8242'_3806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8324''8242'_3806 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7
  = du_lem'8324''8242'_3806 v2 v6 v7
du_lem'8324''8242'_3806 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_lem'8324''8242'_3806 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                        (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)))
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe
                           du_'8743''45'identity'737'_3538 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                              (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                        (coe
                           du_'8743''45'identity'691'_3534 (coe v0)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                              v2))))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (coe
                        MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3306
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))
                           v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
                           (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0))))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v1))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)))
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                           (\ v3 v4 -> v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0)))
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v3 v4 -> v4)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3306
                           (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0))
                           v2))))
               (coe
                  du_lemma'8322'_3776 (coe v0)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2)
                  (coe v1) (coe v2)))
            (coe
               MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
               (coe du_deMorgan'8322'_3634 (coe v0) (coe v1) (coe v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
               (coe
                  du_'172''45'involutive_3606 (coe v0)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
         (coe
            du_deMorgan'8321'_3614 (coe v0)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₄
d_lem'8324'_3808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8324'_3808 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8324'_3808 v2 v5 v6 v7
du_lem'8324'_3808 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8324'_3808 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                       (coe v0)))))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                       (coe
                                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                          (coe v0)))))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                              v3)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           v3)))
                  (coe
                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           v3)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v3)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
                        (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0))))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3204
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0)))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2) v3))
               (coe du_lem'8324''8242'_3806 (coe v0) (coe v2) (coe v3))))
         (coe
            du_deMorgan'8321'_3614 (coe v0) (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v2 v3)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing._.lem₅
d_lem'8325'_3810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lem'8325'_3810 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_lem'8325'_3810 v2 v5 v6 v7
du_lem'8325'_3810 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lem'8325'_3810 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
            v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                              (coe v0)))))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                  v3)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                 (coe v0)))))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                                 (coe
                                    MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                                    (coe v0)))))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                        v3)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                           (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                  (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                        (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
                     v3))))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
            (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                     (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v2))
               v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v1) v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0 v3))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-isMagma
d_'8853''45'isMagma_3812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8853''45'isMagma_3812 ~v0 ~v1 v2 v3 v4
  = du_'8853''45'isMagma_3812 v2 v3 v4
du_'8853''45'isMagma_3812 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8853''45'isMagma_3812 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe du_'8853''45'cong_3666 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-isSemigroup
d_'8853''45'isSemigroup_3814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8853''45'isSemigroup_3814 ~v0 ~v1 v2 v3 v4
  = du_'8853''45'isSemigroup_3814 v2 v3 v4
du_'8853''45'isSemigroup_3814 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8853''45'isSemigroup_3814 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe du_'8853''45'isMagma_3812 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'assoc_3786 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-⊥-isMonoid
d_'8853''45''8869''45'isMonoid_3816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8853''45''8869''45'isMonoid_3816 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8869''45'isMonoid_3816 v2 v3 v4
du_'8853''45''8869''45'isMonoid_3816 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8853''45''8869''45'isMonoid_3816 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe du_'8853''45'isSemigroup_3814 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'identity_3736 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-⊥-isGroup
d_'8853''45''8869''45'isGroup_3818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_'8853''45''8869''45'isGroup_3818 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8869''45'isGroup_3818 v2 v3 v4
du_'8853''45''8869''45'isGroup_3818 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
du_'8853''45''8869''45'isGroup_3818 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1164
      (coe
         du_'8853''45''8869''45'isMonoid_3816 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'inverse_3744 (coe v0) (coe v1) (coe v2))
      (coe (\ v3 v4 v5 -> v5))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-⊥-isAbelianGroup
d_'8853''45''8869''45'isAbelianGroup_3820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'8853''45''8869''45'isAbelianGroup_3820 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8869''45'isAbelianGroup_3820 v2 v3 v4
du_'8853''45''8869''45'isAbelianGroup_3820 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
du_'8853''45''8869''45'isAbelianGroup_3820 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1252
      (coe
         du_'8853''45''8869''45'isGroup_3818 (coe v0) (coe v1) (coe v2))
      (coe du_'8853''45'comm_3680 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-∧-isRing
d_'8853''45''8743''45'isRing_3822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_'8853''45''8743''45'isRing_3822 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8743''45'isRing_3822 v2 v3 v4
du_'8853''45''8743''45'isRing_3822 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
du_'8853''45''8743''45'isRing_3822 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_2876
      (coe
         du_'8853''45''8869''45'isAbelianGroup_3820 (coe v0) (coe v1)
         (coe v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
      (coe du_'8743''45'identity_3540 (coe v0))
      (coe
         du_'8743''45'distrib'45''8853'_3766 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-∧-isCommutativeRing
d_'8853''45''8743''45'isCommutativeRing_3824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888
d_'8853''45''8743''45'isCommutativeRing_3824 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8743''45'isCommutativeRing_3824 v2 v3 v4
du_'8853''45''8743''45'isCommutativeRing_3824 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888
du_'8853''45''8743''45'isCommutativeRing_3824 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_3030
      (coe du_'8853''45''8743''45'isRing_3822 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                  (coe v0)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.XorRing.⊕-∧-commutativeRing
d_'8853''45''8743''45'commutativeRing_3826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4126
d_'8853''45''8743''45'commutativeRing_3826 ~v0 ~v1 v2 v3 v4
  = du_'8853''45''8743''45'commutativeRing_3826 v2 v3 v4
du_'8853''45''8743''45'commutativeRing_3826 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4126
du_'8853''45''8743''45'commutativeRing_3826 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_4352 v1
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 (coe v0))
      (\ v3 -> v3)
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_732 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_730 (coe v0))
      (coe
         du_'8853''45''8743''45'isCommutativeRing_3824 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Lattice.Properties.BooleanAlgebra._⊕_
d__'8853'__3828 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8853'__3828 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.¬-distribʳ-⊕
d_'172''45'distrib'691''45''8853'_3840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'distrib'691''45''8853'_3840 ~v0 ~v1 v2
  = du_'172''45'distrib'691''45''8853'_3840 v2
du_'172''45'distrib'691''45''8853'_3840 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'172''45'distrib'691''45''8853'_3840 v0
  = coe
      du_'172''45'distrib'691''45''8853'_3714 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.¬-distribˡ-⊕
d_'172''45'distrib'737''45''8853'_3842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'distrib'737''45''8853'_3842 ~v0 ~v1 v2
  = du_'172''45'distrib'737''45''8853'_3842 v2
du_'172''45'distrib'737''45''8853'_3842 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'172''45'distrib'737''45''8853'_3842 v0
  = coe
      du_'172''45'distrib'737''45''8853'_3690 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.∧-distrib-⊕
d_'8743''45'distrib'45''8853'_3844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8853'_3844 ~v0 ~v1 v2
  = du_'8743''45'distrib'45''8853'_3844 v2
du_'8743''45'distrib'45''8853'_3844 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'distrib'45''8853'_3844 v0
  = coe
      du_'8743''45'distrib'45''8853'_3766 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.∧-distribʳ-⊕
d_'8743''45'distrib'691''45''8853'_3846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8853'_3846 ~v0 ~v1 v2
  = du_'8743''45'distrib'691''45''8853'_3846 v2
du_'8743''45'distrib'691''45''8853'_3846 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8853'_3846 v0
  = coe
      du_'8743''45'distrib'691''45''8853'_3764 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.∧-distribˡ-⊕
d_'8743''45'distrib'737''45''8853'_3848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8853'_3848 ~v0 ~v1 v2
  = du_'8743''45'distrib'737''45''8853'_3848 v2
du_'8743''45'distrib'737''45''8853'_3848 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8853'_3848 v0
  = coe
      du_'8743''45'distrib'737''45''8853'_3746 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-annihilates-¬
d_'8853''45'annihilates'45''172'_3850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'annihilates'45''172'_3850 ~v0 ~v1 v2
  = du_'8853''45'annihilates'45''172'_3850 v2
du_'8853''45'annihilates'45''172'_3850 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'annihilates'45''172'_3850 v0
  = coe
      du_'8853''45'annihilates'45''172'_3724 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-assoc
d_'8853''45'assoc_3852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'assoc_3852 ~v0 ~v1 v2 = du_'8853''45'assoc_3852 v2
du_'8853''45'assoc_3852 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'assoc_3852 v0
  = coe
      du_'8853''45'assoc_3786 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-comm
d_'8853''45'comm_3854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'comm_3854 ~v0 ~v1 v2 = du_'8853''45'comm_3854 v2
du_'8853''45'comm_3854 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'comm_3854 v0
  = coe
      du_'8853''45'comm_3680 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-cong
d_'8853''45'cong_3856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8853''45'cong_3856 ~v0 ~v1 v2 = du_'8853''45'cong_3856 v2
du_'8853''45'cong_3856 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8853''45'cong_3856 v0
  = coe
      du_'8853''45'cong_3666 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-identity
d_'8853''45'identity_3858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'identity_3858 ~v0 ~v1 v2
  = du_'8853''45'identity_3858 v2
du_'8853''45'identity_3858 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'identity_3858 v0
  = coe
      du_'8853''45'identity_3736 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-identityʳ
d_'8853''45'identity'691'_3860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8853''45'identity'691'_3860 ~v0 ~v1 v2
  = du_'8853''45'identity'691'_3860 v2
du_'8853''45'identity'691'_3860 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8853''45'identity'691'_3860 v0
  = coe
      du_'8853''45'identity'691'_3734 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-identityˡ
d_'8853''45'identity'737'_3862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8853''45'identity'737'_3862 ~v0 ~v1 v2
  = du_'8853''45'identity'737'_3862 v2
du_'8853''45'identity'737'_3862 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8853''45'identity'737'_3862 v0
  = coe
      du_'8853''45'identity'737'_3730 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-inverse
d_'8853''45'inverse_3864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'inverse_3864 ~v0 ~v1 v2 = du_'8853''45'inverse_3864 v2
du_'8853''45'inverse_3864 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'inverse_3864 v0
  = coe
      du_'8853''45'inverse_3744 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-inverseʳ
d_'8853''45'inverse'691'_3866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8853''45'inverse'691'_3866 ~v0 ~v1 v2
  = du_'8853''45'inverse'691'_3866 v2
du_'8853''45'inverse'691'_3866 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8853''45'inverse'691'_3866 v0
  = coe
      du_'8853''45'inverse'691'_3742 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-inverseˡ
d_'8853''45'inverse'737'_3868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
d_'8853''45'inverse'737'_3868 ~v0 ~v1 v2
  = du_'8853''45'inverse'737'_3868 v2
du_'8853''45'inverse'737'_3868 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny
du_'8853''45'inverse'737'_3868 v0
  = coe
      du_'8853''45'inverse'737'_3738 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-isMagma
d_'8853''45'isMagma_3870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8853''45'isMagma_3870 ~v0 ~v1 v2 = du_'8853''45'isMagma_3870 v2
du_'8853''45'isMagma_3870 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8853''45'isMagma_3870 v0
  = coe
      du_'8853''45'isMagma_3812 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-isSemigroup
d_'8853''45'isSemigroup_3872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8853''45'isSemigroup_3872 ~v0 ~v1 v2
  = du_'8853''45'isSemigroup_3872 v2
du_'8853''45'isSemigroup_3872 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8853''45'isSemigroup_3872 v0
  = coe
      du_'8853''45'isSemigroup_3814 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-∧-commutativeRing
d_'8853''45''8743''45'commutativeRing_3874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4126
d_'8853''45''8743''45'commutativeRing_3874 ~v0 ~v1 v2
  = du_'8853''45''8743''45'commutativeRing_3874 v2
du_'8853''45''8743''45'commutativeRing_3874 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4126
du_'8853''45''8743''45'commutativeRing_3874 v0
  = coe
      du_'8853''45''8743''45'commutativeRing_3826 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-∧-isCommutativeRing
d_'8853''45''8743''45'isCommutativeRing_3876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888
d_'8853''45''8743''45'isCommutativeRing_3876 ~v0 ~v1 v2
  = du_'8853''45''8743''45'isCommutativeRing_3876 v2
du_'8853''45''8743''45'isCommutativeRing_3876 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888
du_'8853''45''8743''45'isCommutativeRing_3876 v0
  = coe
      du_'8853''45''8743''45'isCommutativeRing_3824 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-∧-isRing
d_'8853''45''8743''45'isRing_3878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_'8853''45''8743''45'isRing_3878 ~v0 ~v1 v2
  = du_'8853''45''8743''45'isRing_3878 v2
du_'8853''45''8743''45'isRing_3878 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
du_'8853''45''8743''45'isRing_3878 v0
  = coe
      du_'8853''45''8743''45'isRing_3822 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-⊥-isAbelianGroup
d_'8853''45''8869''45'isAbelianGroup_3880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'8853''45''8869''45'isAbelianGroup_3880 ~v0 ~v1 v2
  = du_'8853''45''8869''45'isAbelianGroup_3880 v2
du_'8853''45''8869''45'isAbelianGroup_3880 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
du_'8853''45''8869''45'isAbelianGroup_3880 v0
  = coe
      du_'8853''45''8869''45'isAbelianGroup_3820 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-⊥-isGroup
d_'8853''45''8869''45'isGroup_3882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_'8853''45''8869''45'isGroup_3882 ~v0 ~v1 v2
  = du_'8853''45''8869''45'isGroup_3882 v2
du_'8853''45''8869''45'isGroup_3882 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
du_'8853''45''8869''45'isGroup_3882 v0
  = coe
      du_'8853''45''8869''45'isGroup_3818 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.DefaultXorRing.⊕-⊥-isMonoid
d_'8853''45''8869''45'isMonoid_3884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8853''45''8869''45'isMonoid_3884 ~v0 ~v1 v2
  = du_'8853''45''8869''45'isMonoid_3884 v2
du_'8853''45''8869''45'isMonoid_3884 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8853''45''8869''45'isMonoid_3884 v0
  = coe
      du_'8853''45''8869''45'isMonoid_3816 (coe v0)
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
              (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2))))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_734
                          (coe v0)))))
              (coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__724 v0 v1 v2)
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__728 v0
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__726 v0 v1 v2)))))
-- Algebra.Lattice.Properties.BooleanAlgebra.⊥≉⊤
d_'8869''8777''8868'_3886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny
d_'8869''8777''8868'_3886 ~v0 ~v1 v2
  = du_'8869''8777''8868'_3886 v2
du_'8869''8777''8868'_3886 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny
du_'8869''8777''8868'_3886 v0
  = coe du_'172''8869''8776''8868'_3602 (coe v0)
-- Algebra.Lattice.Properties.BooleanAlgebra.⊤≉⊥
d_'8868''8777''8869'_3888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny
d_'8868''8777''8869'_3888 ~v0 ~v1 v2
  = du_'8868''8777''8869'_3888 v2
du_'8868''8777''8869'_3888 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698 ->
  AgdaAny
du_'8868''8777''8869'_3888 v0
  = coe du_'172''8868''8776''8869'_3604 (coe v0)
