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

module MAlonzo.Code.Data.Integer.Properties where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.Base qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp qualified
import MAlonzo.Code.Algebra.Lattice.Bundles qualified
import MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp qualified
import MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp qualified
import MAlonzo.Code.Algebra.Lattice.Structures qualified
import MAlonzo.Code.Algebra.Morphism.Structures qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Data.Integer.Base qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Nat.Base qualified
import MAlonzo.Code.Data.Nat.Properties qualified
import MAlonzo.Code.Data.Sign.Base qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Morphism.Structures qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Core qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Negation.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Integer.Properties._._DistributesOver_
d__DistributesOver__10 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver__10 = erased
-- Data.Integer.Properties._._DistributesOverʳ_
d__DistributesOver'691'__12 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver'691'__12 = erased
-- Data.Integer.Properties._._DistributesOverˡ_
d__DistributesOver'737'__14 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver'737'__14 = erased
-- Data.Integer.Properties._.Associative
d_Associative_30 :: (Integer -> Integer -> Integer) -> ()
d_Associative_30 = erased
-- Data.Integer.Properties._.Commutative
d_Commutative_34 :: (Integer -> Integer -> Integer) -> ()
d_Commutative_34 = erased
-- Data.Integer.Properties._.Identity
d_Identity_50 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Identity_50 = erased
-- Data.Integer.Properties._.Inverse
d_Inverse_54 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_Inverse_54 = erased
-- Data.Integer.Properties._.LeftIdentity
d_LeftIdentity_76 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftIdentity_76 = erased
-- Data.Integer.Properties._.LeftInverse
d_LeftInverse_78 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_LeftInverse_78 = erased
-- Data.Integer.Properties._.LeftZero
d_LeftZero_84 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftZero_84 = erased
-- Data.Integer.Properties._.RightIdentity
d_RightIdentity_106 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_RightIdentity_106 = erased
-- Data.Integer.Properties._.RightInverse
d_RightInverse_108 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_RightInverse_108 = erased
-- Data.Integer.Properties._.RightZero
d_RightZero_114 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_RightZero_114 = erased
-- Data.Integer.Properties._.Zero
d_Zero_134 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Zero_134 = erased
-- Data.Integer.Properties._.IsAbelianGroup
d_IsAbelianGroup_138 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_150 a0 a1 = ()
-- Data.Integer.Properties._.IsCommutativeRing
d_IsCommutativeRing_152 a0 a1 a2 a3 a4 = ()
-- Data.Integer.Properties._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_154 a0 = ()
-- Data.Integer.Properties._.IsCommutativeSemiring
d_IsCommutativeSemiring_156 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsGroup
d_IsGroup_162 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsMagma
d_IsMagma_182 a0 = ()
-- Data.Integer.Properties._.IsMonoid
d_IsMonoid_188 a0 a1 = ()
-- Data.Integer.Properties._.IsRing
d_IsRing_204 a0 a1 a2 a3 a4 = ()
-- Data.Integer.Properties._.IsSemigroup
d_IsSemigroup_210 a0 = ()
-- Data.Integer.Properties._.IsSemiring
d_IsSemiring_214 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsAbelianGroup.comm
d_comm_230 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_230 = erased
-- Data.Integer.Properties._.IsAbelianGroup.isGroup
d_isGroup_252 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_252 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)
-- Data.Integer.Properties._.IsCommutativeMonoid.comm
d_comm_520 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_520 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_536 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_536 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0)
-- Data.Integer.Properties._.IsCommutativeRing.*-comm
d_'42''45'comm_566 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_566 = erased
-- Data.Integer.Properties._.IsCommutativeRing.isRing
d_isRing_654 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_isRing_654 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0)
-- Data.Integer.Properties._.IsCommutativeSemigroup.comm
d_comm_688 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_688 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_698 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_698 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v0)
-- Data.Integer.Properties._.IsCommutativeSemiring.*-comm
d_'42''45'comm_720 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_720 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.isSemiring
d_isSemiring_790 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_790 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)
-- Data.Integer.Properties._.IsGroup.inverse
d_inverse_918 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_918 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1052 (coe v0)
-- Data.Integer.Properties._.IsGroup.isMonoid
d_isMonoid_932 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_932 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0)
-- Data.Integer.Properties._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_954 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_954 = erased
-- Data.Integer.Properties._.IsMagma.isEquivalence
d_isEquivalence_1482 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1482 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v0)
-- Data.Integer.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1496 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1496 = erased
-- Data.Integer.Properties._.IsMonoid.identity
d_identity_1592 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1592 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_698 (coe v0)
-- Data.Integer.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1604 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1604 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0)
-- Data.Integer.Properties._.IsRing.*-assoc
d_'42''45'assoc_2110 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2110 = erased
-- Data.Integer.Properties._.IsRing.*-cong
d_'42''45'cong_2112 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2112 = erased
-- Data.Integer.Properties._.IsRing.*-identity
d_'42''45'identity_2118 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2118 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2678 (coe v0)
-- Data.Integer.Properties._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2146 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2146 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
      (coe v0)
-- Data.Integer.Properties._.IsRing.distrib
d_distrib_2176 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2176 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2680 (coe v0)
-- Data.Integer.Properties._.IsSemigroup.assoc
d_assoc_2336 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2336 = erased
-- Data.Integer.Properties._.IsSemigroup.isMagma
d_isMagma_2340 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2340 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0)
-- Data.Integer.Properties._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2454 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2454 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe v0)
-- Data.Integer.Properties._.IsSemiring.zero
d_zero_2468 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2468 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1586 (coe v0)
-- Data.Integer.Properties.ℤtoℕ.Homomorphic₀
d_Homomorphic'8320'_2652 ::
  (Integer -> Integer) -> Integer -> Integer -> ()
d_Homomorphic'8320'_2652 = erased
-- Data.Integer.Properties.ℤtoℕ.Homomorphic₁
d_Homomorphic'8321'_2654 ::
  (Integer -> Integer) ->
  (Integer -> Integer) -> (Integer -> Integer) -> ()
d_Homomorphic'8321'_2654 = erased
-- Data.Integer.Properties.ℤtoℕ.Homomorphic₂
d_Homomorphic'8322'_2656 ::
  (Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_Homomorphic'8322'_2656 = erased
-- Data.Integer.Properties.ℤtoℕ.Morphism
d_Morphism_2658 :: ()
d_Morphism_2658 = erased
-- Data.Integer.Properties.ℕtoℤ.Homomorphic₀
d_Homomorphic'8320'_2662 ::
  (Integer -> Integer) -> Integer -> Integer -> ()
d_Homomorphic'8320'_2662 = erased
-- Data.Integer.Properties.ℕtoℤ.Homomorphic₁
d_Homomorphic'8321'_2664 ::
  (Integer -> Integer) ->
  (Integer -> Integer) -> (Integer -> Integer) -> ()
d_Homomorphic'8321'_2664 = erased
-- Data.Integer.Properties.ℕtoℤ.Homomorphic₂
d_Homomorphic'8322'_2666 ::
  (Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_Homomorphic'8322'_2666 = erased
-- Data.Integer.Properties.ℕtoℤ.Morphism
d_Morphism_2668 :: ()
d_Morphism_2668 = erased
-- Data.Integer.Properties.+-injective
d_'43''45'injective_2686 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'injective_2686 = erased
-- Data.Integer.Properties.-[1+-injective
d_'45''91'1'43''45'injective_2688 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45''91'1'43''45'injective_2688 = erased
-- Data.Integer.Properties.+[1+-injective
d_'43''91'1'43''45'injective_2690 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''91'1'43''45'injective_2690 = erased
-- Data.Integer.Properties._≟_
d__'8799'__2692 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__2692 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                  erased erased
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688 (coe v0) (coe v1))
            _ -> coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                    coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                          erased erased
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688 (coe v2)
                             (coe v3))))
-- Data.Integer.Properties.≡-setoid
d_'8801''45'setoid_2710 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8801''45'setoid_2710
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Integer.Properties.≡-decSetoid
d_'8801''45'decSetoid_2712 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8801''45'decSetoid_2712
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__2692)
-- Data.Integer.Properties.drop‿+≤+
d_drop'8255''43''8804''43'_2714 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop'8255''43''8804''43'_2714 ~v0 ~v1 v2
  = du_drop'8255''43''8804''43'_2714 v2
du_drop'8255''43''8804''43'_2714 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_drop'8255''43''8804''43'_2714 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3 -> coe v3
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.drop‿-≤-
d_drop'8255''45''8804''45'_2718 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop'8255''45''8804''45'_2718 ~v0 ~v1 v2
  = du_drop'8255''45''8804''45'_2718 v2
du_drop'8255''45''8804''45'_2718 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_drop'8255''45''8804''45'_2718 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v3 -> coe v3
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.≤-reflexive
d_'8804''45'reflexive_2722 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'reflexive_2722 v0 ~v1 ~v2
  = du_'8804''45'reflexive_2722 v0
du_'8804''45'reflexive_2722 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8804''45'reflexive_2722 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
            (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776 (coe v0))
      _ -> let v1 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776 (coe v1)))
-- Data.Integer.Properties.≤-refl
d_'8804''45'refl_2728 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'refl_2728 v0 = coe du_'8804''45'reflexive_2722 (coe v0)
-- Data.Integer.Properties.≤-trans
d_'8804''45'trans_2730 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'trans_2730 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45'trans_2730 v3 v4
du_'8804''45'trans_2730 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8804''45'trans_2730 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784 (coe v7)
                       (coe v4))
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40)
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784 (coe v4)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.≤-antisym
d_'8804''45'antisym_2744 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_2744 = erased
-- Data.Integer.Properties.≤-total
d_'8804''45'total_2754 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_2754 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Sum.Base.du_map_84
                  (coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48)
                  (coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48)
                  (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'total_2790
                     (coe v0) (coe v1))
            _ -> coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                   (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40)
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                      (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40)
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Sum.Base.du_map_84
                          (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34)
                          (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34)
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'total_2790
                             (coe v3) (coe v2))))
-- Data.Integer.Properties._≤?_
d__'8804''63'__2772 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__2772 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                  (coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48)
                  (coe du_drop'8255''43''8804''43'_2714)
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802 (coe v0)
                     (coe v1))
            _ -> coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                    coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                      (coe
                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                         (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40))
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                          (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34)
                          (coe du_drop'8255''45''8804''45'_2718)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802 (coe v3)
                             (coe v2))))
-- Data.Integer.Properties.≤-irrelevant
d_'8804''45'irrelevant_2790 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_2790 = erased
-- Data.Integer.Properties.≤-isPreorder
d_'8804''45'isPreorder_2800 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_2800
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_2722 v0)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45'trans_2730 v3 v4)
-- Data.Integer.Properties.≤-isTotalPreorder
d_'8804''45'isTotalPreorder_2802 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_'8804''45'isTotalPreorder_2802
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalPreorder'46'constructor_8325
      (coe d_'8804''45'isPreorder_2800) (coe d_'8804''45'total_2754)
-- Data.Integer.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_2804 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8804''45'isPartialOrder_2804
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe d_'8804''45'isPreorder_2800) erased
-- Data.Integer.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_2806 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8804''45'isTotalOrder_2806
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_20555
      (coe d_'8804''45'isPartialOrder_2804) (coe d_'8804''45'total_2754)
-- Data.Integer.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_2808 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8804''45'isDecTotalOrder_2808
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22695
      (coe d_'8804''45'isTotalOrder_2806) (coe d__'8799'__2692)
      (coe d__'8804''63'__2772)
-- Data.Integer.Properties.≤-preorder
d_'8804''45'preorder_2810 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8804''45'preorder_2810
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      d_'8804''45'isPreorder_2800
-- Data.Integer.Properties.≤-totalPreorder
d_'8804''45'totalPreorder_2812 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222
d_'8804''45'totalPreorder_2812
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalPreorder'46'constructor_4573
      d_'8804''45'isTotalPreorder_2802
-- Data.Integer.Properties.≤-poset
d_'8804''45'poset_2814 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8804''45'poset_2814
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      d_'8804''45'isPartialOrder_2804
-- Data.Integer.Properties.≤-totalOrder
d_'8804''45'totalOrder_2816 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_'8804''45'totalOrder_2816
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_15747
      d_'8804''45'isTotalOrder_2806
-- Data.Integer.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_2818 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_'8804''45'decTotalOrder_2818
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17849
      d_'8804''45'isDecTotalOrder_2808
-- Data.Integer.Properties.≤ᵇ⇒≤
d_'8804''7495''8658''8804'_2820 ::
  Integer ->
  Integer -> AgdaAny -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''7495''8658''8804'_2820 v0 v1 ~v2
  = du_'8804''7495''8658''8804'_2820 v0 v1
du_'8804''7495''8658''8804'_2820 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8804''7495''8658''8804'_2820 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2746
               (coe v0))
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
             _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v1) in
                  coe
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2746
                          (coe v2)))
-- Data.Integer.Properties.≤⇒≤ᵇ
d_'8804''8658''8804''7495'_2828 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> AgdaAny
d_'8804''8658''8804''7495'_2828 ~v0 ~v1 v2
  = du_'8804''8658''8804''7495'_2828 v2
du_'8804''8658''8804''7495'_2828 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> AgdaAny
du_'8804''8658''8804''7495'_2828 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2758
             (coe v3)
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2758
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.drop‿+<+
d_drop'8255''43''60''43'_2834 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop'8255''43''60''43'_2834 ~v0 ~v1 v2
  = du_drop'8255''43''60''43'_2834 v2
du_drop'8255''43''60''43'_2834 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_drop'8255''43''60''43'_2834 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v3 -> coe v3
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.drop‿-<-
d_drop'8255''45''60''45'_2838 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop'8255''45''60''45'_2838 ~v0 ~v1 v2
  = du_drop'8255''45''60''45'_2838 v2
du_drop'8255''45''60''45'_2838 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_drop'8255''45''60''45'_2838 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v3 -> coe v3
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.+≮0
d_'43''8814'0_2842 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''8814'0_2842 = erased
-- Data.Integer.Properties.+≮-
d_'43''8814''45'_2844 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''8814''45'_2844 = erased
-- Data.Integer.Properties.<⇒≤
d_'60''8658''8804'_2846 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'60''8658''8804'_2846 ~v0 ~v1 v2 = du_'60''8658''8804'_2846 v2
du_'60''8658''8804'_2846 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'60''8658''8804'_2846 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854 (coe v3))
      MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
        -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
      MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.<⇒≢
d_'60''8658''8802'_2852 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_2852 = erased
-- Data.Integer.Properties.<⇒≱
d_'60''8658''8817'_2858 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_2858 = erased
-- Data.Integer.Properties.≤⇒≯
d_'8804''8658''8815'_2864 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_2864 = erased
-- Data.Integer.Properties.≰⇒>
d_'8816''8658''62'_2874 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8816''8658''62'_2874 v0 v1 ~v2 = du_'8816''8658''62'_2874 v0 v1
du_'8816''8658''62'_2874 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'8816''8658''62'_2874 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_'8816''8658''62'_2888 (coe v0)
                     (coe v1))
            _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                    coe
                      MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                      erased
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8816''8658''62'_2888 (coe v3)
                             (coe v2))))
-- Data.Integer.Properties.≮⇒≥
d_'8814''8658''8805'_2900 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8814''8658''8805'_2900 v0 v1 ~v2
  = du_'8814''8658''8805'_2900 v0 v1
du_'8814''8658''8805'_2900 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8814''8658''8805'_2900 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2902
                     (coe v0) (coe v1))
            _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                    coe
                      MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                      erased
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2902
                             (coe v3) (coe v2))))
-- Data.Integer.Properties.>⇒≰
d_'62''8658''8816'_2926 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''8658''8816'_2926 = erased
-- Data.Integer.Properties.≤∧≢⇒<
d_'8804''8743''8802''8658''60'_2928 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8804''8743''8802''8658''60'_2928 v0 v1 v2 ~v3
  = du_'8804''8743''8802''8658''60'_2928 v0 v1 v2
du_'8804''8743''8802''8658''60'_2928 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'8804''8743''8802''8658''60'_2928 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v5
        -> let v6 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2918
                   (coe v6) (coe v5)))
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2918
                (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.≤∧≮⇒≡
d_'8804''8743''8814''8658''8801'_2940 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  (MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8743''8814''8658''8801'_2940 = erased
-- Data.Integer.Properties.<-irrefl
d_'60''45'irrefl_2946 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_2946 = erased
-- Data.Integer.Properties.<-asym
d_'60''45'asym_2952 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_2952 = erased
-- Data.Integer.Properties.≤-<-trans
d_'8804''45''60''45'trans_2958 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8804''45''60''45'trans_2958 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45''60''45'trans_2958 v3 v4
du_'8804''45''60''45'trans_2958 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'8804''45''60''45'trans_2958 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_2992
                       (coe v7) (coe v4))
             MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986
                       (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.<-≤-trans
d_'60''45''8804''45'trans_2972 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'60''45''8804''45'trans_2972 ~v0 ~v1 ~v2 v3 v4
  = du_'60''45''8804''45'trans_2972 v3 v4
du_'60''45''8804''45'trans_2972 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'60''45''8804''45'trans_2972 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986
                       (coe v7) (coe v4))
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
      MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_2992
                       (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.<-trans
d_'60''45'trans_2986 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'60''45'trans_2986 ~v0 ~v1 ~v2 v3 v4
  = du_'60''45'trans_2986 v3 v4
du_'60''45'trans_2986 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'60''45'trans_2986 v0 v1
  = coe
      du_'8804''45''60''45'trans_2958
      (coe du_'60''8658''8804'_2846 (coe v0)) (coe v1)
-- Data.Integer.Properties.<-cmp
d_'60''45'cmp_2992 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_2992 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          let v2
                = coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64) in
          coe
            (case coe v0 of
               0 -> case coe v1 of
                      0 -> coe
                             MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
                      _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                          coe
                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                            (coe
                               MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                               (coe
                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                  (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                      _ -> coe v2
               _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                    coe
                      (case coe v1 of
                         0 -> coe
                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                                   (coe
                                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                         _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                             let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                             coe
                               (let v5
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                                          erased
                                          (\ v5 ->
                                             coe
                                               MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2678
                                               (coe v3))
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                             (coe eqInt (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                                (coe eqInt (coe v0) (coe v1)))) in
                                coe
                                  (case coe v5 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                                       -> if coe v6
                                            then coe
                                                   seq (coe v7)
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                                                      erased)
                                            else (let v8
                                                        = seq
                                                            (coe v7)
                                                            (let v8 = ltInt (coe v0) (coe v1) in
                                                             coe
                                                               (if coe v8
                                                                  then coe
                                                                         seq
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                                                            (coe v8))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                                            (coe
                                                                               MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2716
                                                                               (coe v3)))
                                                                  else coe
                                                                         seq
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                                                            (coe v8))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                                            (coe
                                                                               MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2918
                                                                               (coe v3)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2902
                                                                                  (coe v3)
                                                                                  (coe v4)))))) in
                                                  coe
                                                    (case coe v8 of
                                                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v9
                                                         -> coe
                                                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                    v9))
                                                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v10
                                                         -> coe
                                                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                                                              erased
                                                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v11
                                                         -> coe
                                                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                    v11))
                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                         _ -> coe
                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)))
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                    coe
                      MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                      (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (let v4
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                                  erased
                                  (\ v4 ->
                                     coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2678
                                       (coe v2))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe eqInt (coe v0) (coe v1))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                        (coe eqInt (coe v0) (coe v1)))) in
                        coe
                          (case coe v4 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                               -> if coe v5
                                    then coe
                                           seq (coe v6)
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                                              erased)
                                    else (let v7
                                                = seq
                                                    (coe v6)
                                                    (let v7 = ltInt (coe v1) (coe v0) in
                                                     coe
                                                       (if coe v7
                                                          then coe
                                                                 seq
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                                                    (coe v7))
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2716
                                                                       (coe v2)))
                                                          else coe
                                                                 seq
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                                                    (coe v7))
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2918
                                                                       (coe v2)
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2902
                                                                          (coe v2) (coe v3)))))) in
                                          coe
                                            (case coe v7 of
                                               MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v8
                                                 -> coe
                                                      MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                      (coe
                                                         MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                                                         v8)
                                               MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v9
                                                 -> coe
                                                      MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                                                      erased
                                               MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v10
                                                 -> coe
                                                      MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                      (coe
                                                         MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                                                         v10)
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
-- Data.Integer.Properties._<?_
d__'60''63'__3082 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__3082 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                  (coe MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72)
                  (coe du_drop'8255''43''60''43'_2834)
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3030 (coe v0)
                     (coe v1))
            _ -> coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                    coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                      (coe
                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                         (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64))
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                          (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58)
                          (coe du_drop'8255''45''60''45'_2838)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3030 (coe v3)
                             (coe v2))))
-- Data.Integer.Properties.<-irrelevant
d_'60''45'irrelevant_3100 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_3100 = erased
-- Data.Integer.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_3110 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_3110
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_2986 v3 v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4)))
-- Data.Integer.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_3116 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder_3116
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe d_'60''45'isStrictPartialOrder_3110) (coe d_'60''45'cmp_2992)
-- Data.Integer.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_3118 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_3118
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11097
      d_'60''45'isStrictPartialOrder_3110
-- Data.Integer.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_3120 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder_3120
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_21059
      d_'60''45'isStrictTotalOrder_3116
-- Data.Integer.Properties.i≮i
d_i'8814'i_3122 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_i'8814'i_3122 = erased
-- Data.Integer.Properties.>-irrefl
d_'62''45'irrefl_3124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''45'irrefl_3124 = erased
-- Data.Integer.Properties.≤-Reasoning._._IsRelatedTo_
d__IsRelatedTo__3130 a0 a1 = ()
-- Data.Integer.Properties.≤-Reasoning._._∎
d__'8718'_3132 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_3132
  = let v0 = d_'8804''45'isPreorder_2800 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
            (coe v0)))
-- Data.Integer.Properties.≤-Reasoning._.<-go
d_'60''45'go_3134 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_3134
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_2986 v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45''8804''45'trans_2972 v3 v4)
-- Data.Integer.Properties.≤-Reasoning._.IsEquality
d_IsEquality_3136 a0 a1 a2 = ()
-- Data.Integer.Properties.≤-Reasoning._.IsEquality?
d_IsEquality'63'_3138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_3138 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
      v2
-- Data.Integer.Properties.≤-Reasoning._.IsStrict
d_IsStrict_3140 a0 a1 a2 = ()
-- Data.Integer.Properties.≤-Reasoning._.IsStrict?
d_IsStrict'63'_3142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_3142 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
      v2
-- Data.Integer.Properties.≤-Reasoning._.begin_
d_begin__3144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_begin__3144
  = let v0 = d_'8804''45'isPreorder_2800 in
    coe
      (let v1 = \ v1 v2 v3 -> coe du_'60''8658''8804'_2846 v3 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe v0) (coe v1))))
-- Data.Integer.Properties.≤-Reasoning._.begin-contradiction_
d_begin'45'contradiction__3146 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d_begin'45'contradiction__3146 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
-- Data.Integer.Properties.≤-Reasoning._.begin_
d_begin__3148 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__3148 = erased
-- Data.Integer.Properties.≤-Reasoning._.begin_
d_begin__3150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_begin__3150
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Data.Integer.Properties.≤-Reasoning._.eqRelation
d_eqRelation_3152 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_3152
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
-- Data.Integer.Properties.≤-Reasoning._.extractEquality
d_extractEquality_3156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractEquality_3156 = erased
-- Data.Integer.Properties.≤-Reasoning._.extractStrict
d_extractStrict_3158 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_extractStrict_3158 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
      v2 v3
-- Data.Integer.Properties.≤-Reasoning._.start
d_start_3166 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_start_3166
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
      (coe d_'8804''45'isPreorder_2800)
      (\ v0 v1 v2 -> coe du_'60''8658''8804'_2846 v2)
-- Data.Integer.Properties.≤-Reasoning._.step-<
d_step'45''60'_3168 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_3168
  = let v0 = \ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_2986 v3 v4 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160 in
       coe
         (let v2
                = \ v2 v3 v4 v5 v6 -> coe du_'60''45''8804''45'trans_2972 v5 v6 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe v0) (coe v1) (coe v2)))))
-- Data.Integer.Properties.≤-Reasoning._.step-≡
d_step'45''8801'_3170 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_3170
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Integer.Properties.≤-Reasoning._.step-≡-∣
d_step'45''8801''45''8739'_3172 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_3172 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_3172 v2
du_step'45''8801''45''8739'_3172 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_3172 v0 = coe v0
-- Data.Integer.Properties.≤-Reasoning._.step-≡-⟨
d_step'45''8801''45''10216'_3174 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_3174
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Integer.Properties.≤-Reasoning._.step-≡-⟩
d_step'45''8801''45''10217'_3176 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_3176
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Integer.Properties.≤-Reasoning._.step-≡˘
d_step'45''8801''728'_3178 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_3178
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Integer.Properties.≤-Reasoning._.step-≤
d_step'45''8804'_3180 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_3180
  = let v0 = d_'8804''45'isPreorder_2800 in
    coe
      (let v1
             = \ v1 v2 v3 v4 v5 -> coe du_'8804''45''60''45'trans_2958 v4 v5 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe v0) (coe v1))))
-- Data.Integer.Properties.≤-Reasoning._.stop
d_stop_3182 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_3182
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
      (coe d_'8804''45'isPreorder_2800)
-- Data.Integer.Properties.≤-Reasoning._.strictRelation
d_strictRelation_3186 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_3186
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
-- Data.Integer.Properties.≤-Reasoning._.≈-go
d_'8776''45'go_3188 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_3188
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
      (coe d_'8804''45'isPreorder_2800)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
-- Data.Integer.Properties.≤-Reasoning._.≡-go
d_'8801''45'go_3190 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_3190 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_3190 v4
du_'8801''45'go_3190 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_3190 v0 = coe v0
-- Data.Integer.Properties.≤-Reasoning._.≤-go
d_'8804''45'go_3192 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_3192
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
      (coe d_'8804''45'isPreorder_2800)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45''60''45'trans_2958 v3 v4)
-- Data.Integer.Properties.positive⁻¹
d_positive'8315''185'_3212 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_positive'8315''185'_3212 ~v0 ~v1 = du_positive'8315''185'_3212
du_positive'8315''185'_3212 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_positive'8315''185'_3212
  = coe
      MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Data.Integer.Properties.negative⁻¹
d_negative'8315''185'_3218 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_negative'8315''185'_3218 ~v0 ~v1 = du_negative'8315''185'_3218
du_negative'8315''185'_3218 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_negative'8315''185'_3218
  = coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
-- Data.Integer.Properties.nonPositive⁻¹
d_nonPositive'8315''185'_3224 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_nonPositive'8315''185'_3224 v0 ~v1
  = du_nonPositive'8315''185'_3224 v0
du_nonPositive'8315''185'_3224 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_nonPositive'8315''185'_3224 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
-- Data.Integer.Properties.nonNegative⁻¹
d_nonNegative'8315''185'_3230 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_nonNegative'8315''185'_3230 ~v0 ~v1
  = du_nonNegative'8315''185'_3230
du_nonNegative'8315''185'_3230 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_nonNegative'8315''185'_3230
  = coe
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Data.Integer.Properties.negative<positive
d_negative'60'positive_3238 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_negative'60'positive_3238 ~v0 ~v1 ~v2 ~v3
  = du_negative'60'positive_3238
du_negative'60'positive_3238 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_negative'60'positive_3238
  = coe
      du_'60''45'trans_2986 (coe du_negative'8315''185'_3218)
      (coe du_positive'8315''185'_3212)
-- Data.Integer.Properties.neg-involutive
d_neg'45'involutive_3246 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'involutive_3246 = erased
-- Data.Integer.Properties.neg-injective
d_neg'45'injective_3252 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'injective_3252 = erased
-- Data.Integer.Properties.neg-≤-pos
d_neg'45''8804''45'pos_3268 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_neg'45''8804''45'pos_3268 v0 ~v1
  = du_neg'45''8804''45'pos_3268 v0
du_neg'45''8804''45'pos_3268 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_neg'45''8804''45'pos_3268 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
-- Data.Integer.Properties.neg-mono-≤
d_neg'45'mono'45''8804'_3272 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_neg'45'mono'45''8804'_3272 ~v0 v1 v2
  = du_neg'45'mono'45''8804'_3272 v1 v2
du_neg'45'mono'45''8804'_3272 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_neg'45'mono'45''8804'_3272 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4)
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe du_neg'45''8804''45'pos_3268 (coe v0)
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe du_neg'45''8804''45'pos_3268 (coe v0)
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.neg-cancel-≤
d_neg'45'cancel'45''8804'_3278 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_neg'45'cancel'45''8804'_3278 v0 v1 v2
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                    (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          case coe v1 of
            0 -> coe
                   seq (coe v2)
                   (coe
                      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
            _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                case coe v2 of
                  MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v5
                    -> coe
                         MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                         (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
                  _ -> MAlonzo.RTE.mazUnreachableError
            _ -> coe
                   seq (coe v2)
                   (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40)
      _ -> case coe v2 of
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
               -> case coe v5 of
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                      -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.neg-mono-<
d_neg'45'mono'45''60'_3302 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_neg'45'mono'45''60'_3302 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v2) (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          case coe v2 of
            MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v5
              -> coe
                   MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                   (coe MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70 (coe v5))
            _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v1 of
             0 -> coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
             _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                 coe
                   seq (coe v2) (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
             _ -> case coe v2 of
                    MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v5
                      -> coe
                           MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                           (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.neg-cancel-<
d_neg'45'cancel'45''60'_3316 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_neg'45'cancel'45''60'_3316 v0 v1 v2
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          case coe v1 of
            0 -> coe
                   seq (coe v2)
                   (coe
                      MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                      (coe
                         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
            _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                case coe v2 of
                  MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v5
                    -> coe
                         MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                         (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
                  _ -> MAlonzo.RTE.mazUnreachableError
            _ -> coe
                   seq (coe v2) (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
      _ -> case coe v2 of
             MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v5
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                    (coe MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.∣i∣≡0⇒i≡0
d_'8739'i'8739''8801'0'8658'i'8801'0_3340 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'i'8739''8801'0'8658'i'8801'0_3340 = erased
-- Data.Integer.Properties.∣-i∣≡∣i∣
d_'8739''45'i'8739''8801''8739'i'8739'_3344 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45'i'8739''8801''8739'i'8739'_3344 = erased
-- Data.Integer.Properties.0≤i⇒+∣i∣≡i
d_0'8804'i'8658''43''8739'i'8739''8801'i_3350 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8804'i'8658''43''8739'i'8739''8801'i_3350 = erased
-- Data.Integer.Properties.+∣i∣≡i⇒0≤i
d_'43''8739'i'8739''8801'i'8658'0'8804'i_3352 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''8739'i'8739''8801'i'8658'0'8804'i_3352 ~v0 ~v1
  = du_'43''8739'i'8739''8801'i'8658'0'8804'i_3352
du_'43''8739'i'8739''8801'i'8658'0'8804'i_3352 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'43''8739'i'8739''8801'i'8658'0'8804'i_3352
  = coe
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Data.Integer.Properties.+∣i∣≡i⊎+∣i∣≡-i
d_'43''8739'i'8739''8801'i'8846''43''8739'i'8739''8801''45'i_3358 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'43''8739'i'8739''8801'i'8846''43''8739'i'8739''8801''45'i_3358 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Integer.Properties.∣m⊝n∣≤m⊔n
d_'8739'm'8861'n'8739''8804'm'8852'n_3368 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'8861'n'8739''8804'm'8852'n_3368 v0 v1
  = let v2 = ltInt (coe v0) (coe v1) in
    coe
      (if coe v2
         then coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                   (\ v3 v4 v5 ->
                      coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854 v5))
                (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d_'45'__252
                      (coe subInt (coe v1) (coe v0))))
                (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                   (\ v3 v4 v5 v6 v7 -> v7)
                   (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d_'45'__252
                         (coe subInt (coe v1) (coe v0))))
                   (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                      (coe subInt (coe v1) (coe v0)))
                   (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                         (\ v3 v4 v5 v6 v7 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v6
                              v7))
                      (subInt (coe v1) (coe v0)) v1
                      (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                            (\ v3 v4 v5 v6 v7 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v6
                                 v7))
                         v1 (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                         (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810))
                            (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1)))
                         (let v3
                                = MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2822 in
                          coe
                            (let v4
                                   = MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4440 in
                             coe
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                                     (coe v3))
                                  (coe
                                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                                     (coe v4))
                                  (coe v0) (coe v1)))))
                      (MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5042
                         (coe v1) (coe v0)))
                   erased)
         else coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                   (\ v3 v4 v5 ->
                      coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854 v5))
                (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                   (coe subInt (coe v0) (coe v1)))
                (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                      (\ v3 v4 v5 v6 v7 ->
                         coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v6
                           v7))
                   (subInt (coe v0) (coe v1)) v0
                   (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                         (\ v3 v4 v5 v6 v7 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v6
                              v7))
                      v0 (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                      (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810))
                         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v1)))
                      (let v3
                             = MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2822 in
                       coe
                         (let v4
                                = MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4440 in
                          coe
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
                               (coe
                                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                                  (coe v3))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                                  (coe v4))
                               (coe v0) (coe v1)))))
                   (MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5042
                      (coe v0) (coe v1))))
-- Data.Integer.Properties.∣i+j∣≤∣i∣+∣j∣
d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3398 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3398 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe (0 :: Integer))
                      (coe v1))))
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v0) (coe v1)))
            _ -> coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                      (\ v2 v3 v4 ->
                         coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854 v4))
                   (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v0) (coe v1)))
                   (addInt
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                         (\ v2 v3 v4 v5 v6 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v5
                              v6))
                      (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0)
                            (coe subInt (coe (0 :: Integer)) (coe v1))))
                      (MAlonzo.Code.Data.Nat.Base.d__'8852'__204
                         (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1)))
                      (addInt
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                            (\ v2 v3 v4 v5 v6 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v5
                                 v6))
                         (MAlonzo.Code.Data.Nat.Base.d__'8852'__204
                            (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1)))
                         (subInt (coe v0) (coe v1))
                         (addInt
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810))
                            (coe subInt (coe v0) (coe v1)))
                         (MAlonzo.Code.Data.Nat.Properties.d_m'8852'n'8804'm'43'n_4830
                            (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))))
                      (d_'8739'm'8861'n'8739''8804'm'8852'n_3368
                         (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))))
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                      (\ v2 v3 v4 ->
                         coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854 v4))
                   (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v0) (coe v1)))
                   (addInt
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                         (\ v2 v3 v4 v5 v6 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v5
                              v6))
                      (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v1)
                            (coe subInt (coe (0 :: Integer)) (coe v0))))
                      (MAlonzo.Code.Data.Nat.Base.d__'8852'__204
                         (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0)))
                      (addInt
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                            (\ v2 v3 v4 v5 v6 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v5
                                 v6))
                         (MAlonzo.Code.Data.Nat.Base.d__'8852'__204
                            (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0)))
                         (subInt (coe v1) (coe v0))
                         (addInt
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                            (\ v2 v3 v4 v5 v6 -> v6) (subInt (coe v1) (coe v0))
                            (subInt (coe v1) (coe v0))
                            (addInt
                               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810))
                               (coe subInt (coe v1) (coe v0)))
                            erased)
                         (MAlonzo.Code.Data.Nat.Properties.d_m'8852'n'8804'm'43'n_4830
                            (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0))))
                      (d_'8739'm'8861'n'8739''8804'm'8852'n_3368
                         (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0))))
             _ -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                    (coe subInt (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1))
-- Data.Integer.Properties.∣i-j∣≤∣i∣+∣j∣
d_'8739'i'45'j'8739''8804''8739'i'8739''43''8739'j'8739'_3436 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'i'45'j'8739''8804''8739'i'8739''43''8739'j'8739'_3436 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
         (\ v2 v3 v4 ->
            coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854 v4))
      (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1)))
      (addInt
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
            (\ v2 v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v5
                 v6))
         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1)))
         (addInt
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
         (addInt
            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v2 v3 v4 v5 v6 -> v6)
            (addInt
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
            (addInt
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
            (addInt
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810))
               (coe
                  addInt
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))))
            erased)
         (d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3398
            (coe v0)
            (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1))))
-- Data.Integer.Properties.◃-nonZero
d_'9667''45'nonZero_3454 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'9667''45'nonZero_3454 v0 ~v1 ~v2 = du_'9667''45'nonZero_3454 v0
du_'9667''45'nonZero_3454 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_'9667''45'nonZero_3454 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Integer.Properties.◃-inverse
d_'9667''45'inverse_3458 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45'inverse_3458 = erased
-- Data.Integer.Properties.◃-cong
d_'9667''45'cong_3464 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45'cong_3464 = erased
-- Data.Integer.Properties.+◃n≡+n
d_'43''9667'n'8801''43'n_3480 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''9667'n'8801''43'n_3480 = erased
-- Data.Integer.Properties.-◃n≡-n
d_'45''9667'n'8801''45'n_3484 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45''9667'n'8801''45'n_3484 = erased
-- Data.Integer.Properties.sign-◃
d_sign'45''9667'_3492 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45''9667'_3492 = erased
-- Data.Integer.Properties.abs-◃
d_abs'45''9667'_3498 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45''9667'_3498 = erased
-- Data.Integer.Properties.signᵢ◃∣i∣≡i
d_sign'7522''9667''8739'i'8739''8801'i_3506 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'7522''9667''8739'i'8739''8801'i_3506 = erased
-- Data.Integer.Properties.sign-cong
d_sign'45'cong_3516 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45'cong_3516 = erased
-- Data.Integer.Properties.sign-cong′
d_sign'45'cong'8242'_3532 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sign'45'cong'8242'_3532 v0 v1 ~v2 ~v3 ~v4
  = du_sign'45'cong'8242'_3532 v0 v1
du_sign'45'cong'8242'_3532 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sign'45'cong'8242'_3532 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> let v2
                 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased in
           coe (coe seq (coe v0) (coe v2))
-- Data.Integer.Properties.abs-cong
d_abs'45'cong_3566 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'cong_3566 = erased
-- Data.Integer.Properties.∣s◃m∣*∣t◃n∣≡m*n
d_'8739's'9667'm'8739''42''8739't'9667'n'8739''8801'm'42'n_3590 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739's'9667'm'8739''42''8739't'9667'n'8739''8801'm'42'n_3590
  = erased
-- Data.Integer.Properties.+◃-mono-<
d_'43''9667''45'mono'45''60'_3600 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''9667''45'mono'45''60'_3600 v0 ~v1 v2
  = du_'43''9667''45'mono'45''60'_3600 v0 v2
du_'43''9667''45'mono'45''60'_3600 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'43''9667''45'mono'45''60'_3600 v0 v1
  = coe
      seq (coe v0)
      (coe MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v1)
-- Data.Integer.Properties.+◃-cancel-<
d_'43''9667''45'cancel'45''60'_3612 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''9667''45'cancel'45''60'_3612 v0 ~v1 v2
  = du_'43''9667''45'cancel'45''60'_3612 v0 v2
du_'43''9667''45'cancel'45''60'_3612 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''9667''45'cancel'45''60'_3612 v0 v1
  = coe
      seq (coe v0)
      (case coe v1 of
         MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v4 -> coe v4
         _                                                   -> MAlonzo.RTE.mazUnreachableError)
-- Data.Integer.Properties.neg◃-cancel-<
d_neg'9667''45'cancel'45''60'_3626 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_neg'9667''45'cancel'45''60'_3626 ~v0 v1 v2
  = du_neg'9667''45'cancel'45''60'_3626 v1 v2
du_neg'9667''45'cancel'45''60'_3626 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_neg'9667''45'cancel'45''60'_3626 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v4
               -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.-◃<+◃
d_'45''9667''60''43''9667'_3642 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'45''9667''60''43''9667'_3642 ~v0 v1 ~v2
  = du_'45''9667''60''43''9667'_3642 v1
du_'45''9667''60''43''9667'_3642 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'45''9667''60''43''9667'_3642 v0
  = coe
      seq (coe v0) (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
-- Data.Integer.Properties.+◃≮-◃
d_'43''9667''8814''45''9667'_3644 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''9667''8814''45''9667'_3644 = erased
-- Data.Integer.Properties.n⊖n≡0
d_n'8854'n'8801'0_3650 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8854'n'8801'0_3650 = erased
-- Data.Integer.Properties.[1+m]⊖[1+n]≡m⊖n
d_'91'1'43'm'93''8854''91'1'43'n'93''8801'm'8854'n_3668 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'1'43'm'93''8854''91'1'43'n'93''8801'm'8854'n_3668 = erased
-- Data.Integer.Properties.⊖-swap
d_'8854''45'swap_3690 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'swap_3690 = erased
-- Data.Integer.Properties.⊖-≥
d_'8854''45''8805'_3704 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45''8805'_3704 = erased
-- Data.Integer.Properties.≤-⊖
d_'8804''45''8854'_3732 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45''8854'_3732 = erased
-- Data.Integer.Properties.⊖-≤
d_'8854''45''8804'_3746 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45''8804'_3746 = erased
-- Data.Integer.Properties.⊖-<
d_'8854''45''60'_3782 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45''60'_3782 = erased
-- Data.Integer.Properties.⊖-≰
d_'8854''45''8816'_3784 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45''8816'_3784 = erased
-- Data.Integer.Properties.∣⊖∣-≤
d_'8739''8854''8739''45''8804'_3786 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8854''8739''45''8804'_3786 = erased
-- Data.Integer.Properties.∣⊖∣-<
d_'8739''8854''8739''45''60'_3798 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8854''8739''45''60'_3798 = erased
-- Data.Integer.Properties.∣⊖∣-≰
d_'8739''8854''8739''45''8816'_3810 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8854''8739''45''8816'_3810 = erased
-- Data.Integer.Properties.-m+n≡n⊖m
d_'45'm'43'n'8801'n'8854'm_3816 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45'm'43'n'8801'n'8854'm_3816 = erased
-- Data.Integer.Properties.m-n≡m⊖n
d_m'45'n'8801'm'8854'n_3828 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'45'n'8801'm'8854'n_3828 = erased
-- Data.Integer.Properties.-[n⊖m]≡-m+n
d_'45''91'n'8854'm'93''8801''45'm'43'n_3842 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45''91'n'8854'm'93''8801''45'm'43'n_3842 = erased
-- Data.Integer.Properties.∣m⊖n∣≡∣n⊖m∣
d_'8739'm'8854'n'8739''8801''8739'n'8854'm'8739'_3876 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'8854'n'8739''8801''8739'n'8854'm'8739'_3876 = erased
-- Data.Integer.Properties.+-cancelˡ-⊖
d_'43''45'cancel'737''45''8854'_3892 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'737''45''8854'_3892 = erased
-- Data.Integer.Properties.m⊖n≤m
d_m'8854'n'8804'm_3912 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8854'n'8804'm_3912 v0 v1
  = case coe v1 of
      0 -> coe
             d_'8804''45'refl_2728
             (coe
                MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0)
                (coe (0 :: Integer)))
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                             (coe d_'8804''45'isPreorder_2800)
                             (\ v4 v5 v6 -> coe du_'60''8658''8804'_2846 v6))
                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0) (coe v1))
                          v0
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                             (\ v4 v5 v6 v7 v8 -> v8)
                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0) (coe v1))
                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v3) (coe v2))
                             v0
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                   (coe d_'8804''45'isPreorder_2800)
                                   (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_2958 v7 v8))
                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v3) (coe v2))
                                v3 v0
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                      (coe d_'8804''45'isPreorder_2800)
                                      (\ v4 v5 v6 v7 v8 ->
                                         coe du_'8804''45''60''45'trans_2958 v7 v8))
                                   v3 v0 v0
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                         (coe d_'8804''45'isPreorder_2800))
                                      (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                                      (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2844
                                         (coe v3))))
                                (d_m'8854'n'8804'm_3912 (coe v3) (coe v2)))
                             erased)))
-- Data.Integer.Properties.m⊖n<1+m
d_m'8854'n'60'1'43'm_3930 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_m'8854'n'60'1'43'm_3930 v0 v1
  = coe
      du_'8804''45''60''45'trans_2958
      (coe d_m'8854'n'8804'm_3912 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'60'n'43'm_3630 (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Data.Integer.Properties.m⊖1+n<m
d_m'8854'1'43'n'60'm_3942 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_m'8854'1'43'n'60'm_3942 v0 v1 ~v2
  = du_m'8854'1'43'n'60'm_3942 v0 v1
du_m'8854'1'43'n'60'm_3942 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_m'8854'1'43'n'60'm_3942 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v3 = subInt (coe v1) (coe (1 :: Integer)) in
              coe
                (let v4
                       = coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                      (coe v4)
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0) (coe v1))
                      (coe v0)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                         (\ v5 v6 v7 v8 v9 -> v9)
                         (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0) (coe v1))
                         (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v2) (coe v3))
                         v0
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                               (\ v5 v6 v7 v8 v9 -> coe du_'60''45'trans_2986 v8 v9)
                               (coe
                                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                               (\ v5 v6 v7 v8 v9 -> coe du_'60''45''8804''45'trans_2972 v8 v9))
                            (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v2) (coe v3))
                            v0 v0
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                  (coe d_'8804''45'isPreorder_2800))
                               (coe v0))
                            (d_m'8854'n'60'1'43'm_3930 (coe v2) (coe v3)))
                         erased))))
-- Data.Integer.Properties.-1+m<n⊖m
d_'45'1'43'm'60'n'8854'm_3958 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'45'1'43'm'60'n'8854'm_3958 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776 (coe v0))
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (let v4
                              = coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                        coe
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                             (coe v4) (coe subInt (coe (-1 :: Integer)) (coe v0))
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v1) (coe v0))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                   (\ v5 v6 v7 v8 v9 -> coe du_'60''45'trans_2986 v8 v9)
                                   (coe
                                      MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                   (\ v5 v6 v7 v8 v9 -> coe du_'60''45''8804''45'trans_2972 v8 v9))
                                (subInt (coe (-1 :: Integer)) (coe v0))
                                (subInt (coe (0 :: Integer)) (coe v0))
                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v1) (coe v0))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                      (\ v5 v6 v7 v8 v9 -> coe du_'60''45'trans_2986 v8 v9)
                                      (coe
                                         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                      (\ v5 v6 v7 v8 v9 ->
                                         coe du_'60''45''8804''45'trans_2972 v8 v9))
                                   (subInt (coe (0 :: Integer)) (coe v0))
                                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v3) (coe v2))
                                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v1) (coe v0))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                      (\ v5 v6 v7 v8 v9 -> v9)
                                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                         (coe v3) (coe v2))
                                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                         (coe v1) (coe v0))
                                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                         (coe v1) (coe v0))
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                            (coe d_'8804''45'isPreorder_2800))
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v1)
                                            (coe v0)))
                                      erased)
                                   (d_'45'1'43'm'60'n'8854'm_3958 (coe v2) (coe v3)))
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                                      (coe v0)))))))
-- Data.Integer.Properties.-[1+m]≤n⊖m+1
d_'45''91'1'43'm'93''8804'n'8854'm'43'1_3976 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'45''91'1'43'm'93''8804'n'8854'm'43'1_3976 v0 v1
  = case coe v1 of
      0 -> coe
             d_'8804''45'refl_2728 (coe subInt (coe (-1 :: Integer)) (coe v0))
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe d_'8804''45'isPreorder_2800)
                   (\ v3 v4 v5 -> coe du_'60''8658''8804'_2846 v5))
                (subInt (coe (-1 :: Integer)) (coe v0))
                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                   (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                      (coe d_'8804''45'isPreorder_2800)
                      (\ v3 v4 v5 v6 v7 -> coe du_'8804''45''60''45'trans_2958 v6 v7))
                   (subInt (coe (-1 :: Integer)) (coe v0))
                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v2) (coe v0))
                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                      (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                      (\ v3 v4 v5 v6 v7 -> v7)
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v2) (coe v0))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                         (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                         (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe d_'8804''45'isPreorder_2800))
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v1)
                            (coe addInt (coe (1 :: Integer)) (coe v0))))
                      erased)
                   (coe
                      du_'60''8658''8804'_2846
                      (coe d_'45'1'43'm'60'n'8854'm_3958 (coe v0) (coe v2)))))
-- Data.Integer.Properties.-1+m≤n⊖m
d_'45'1'43'm'8804'n'8854'm_3992 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'45'1'43'm'8804'n'8854'm_3992 v0 v1
  = coe
      du_'60''8658''8804'_2846
      (coe d_'45'1'43'm'60'n'8854'm_3958 (coe v0) (coe v1))
-- Data.Integer.Properties.0⊖m≤+
d_0'8854'm'8804''43'_4002 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_0'8854'm'8804''43'_4002 v0 ~v1 = du_0'8854'm'8804''43'_4002 v0
du_0'8854'm'8804''43'_4002 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_0'8854'm'8804''43'_4002 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
-- Data.Integer.Properties.sign-⊖-<
d_sign'45''8854''45''60'_4006 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45''8854''45''60'_4006 = erased
-- Data.Integer.Properties.sign-⊖-≰
d_sign'45''8854''45''8816'_4018 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45''8854''45''8816'_4018 = erased
-- Data.Integer.Properties.⊖-monoʳ-≥-≤
d_'8854''45'mono'691''45''8805''45''8804'_4024 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8854''45'mono'691''45''8805''45''8804'_4024 v0 v1 v2 v3
  = case coe v0 of
      0 -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe du_0'8854'm'8804''43'_4002 (coe v1)
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       seq (coe v3)
                       (coe
                          d_'8804''45'refl_2728
                          (coe
                             MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0))
                             (\ v5 v6 -> v5) (0 :: Integer) (0 :: Integer)))
                _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                            -> coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                    (coe d_'8804''45'isPreorder_2800)
                                    (\ v7 v8 v9 -> coe du_'60''8658''8804'_2846 v9))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0))
                                    (\ v7 v8 -> v7) v1 (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                    (\ v7 v8 -> v8)
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0)) v1
                                    (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                    (\ v7 v8 v9 v10 v11 -> v11)
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                       (coe v0) (coe v1))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                       (coe v4) (coe v5))
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v7 v8 -> v8)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0)) v1
                                       (0 :: Integer))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                          (\ v7 v8 v9 v10 v11 -> coe du_'60''45'trans_2986 v10 v11)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                          (\ v7 v8 v9 v10 v11 ->
                                             coe du_'60''45''8804''45'trans_2972 v10 v11))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v4) (coe v5))
                                       v0
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v7 v8 -> v8)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0))
                                          v1 (0 :: Integer))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                             (coe d_'8804''45'isPreorder_2800))
                                          (coe v0))
                                       (d_m'8854'n'60'1'43'm_3930 (coe v4) (coe v5)))
                                    erased)
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                            -> let v9 = subInt (coe v2) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                       (coe d_'8804''45'isPreorder_2800)
                                       (\ v10 v11 v12 -> coe du_'60''8658''8804'_2846 v12))
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0))
                                       (\ v10 v11 -> v10) v1 v2)
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v10 v11 -> v11)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0)) v1
                                       v2)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                       (\ v10 v11 v12 v13 v14 -> v14)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v0) (coe v1))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v4) (coe v5))
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v10 v11 -> v11)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0))
                                          v1 v2)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                             (coe d_'8804''45'isPreorder_2800)
                                             (\ v10 v11 v12 v13 v14 ->
                                                coe du_'8804''45''60''45'trans_2958 v13 v14))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v4) (coe v5))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v4) (coe v9))
                                          (coe
                                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                             (\ v10 v11 -> v11)
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v0))
                                             v1 v2)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                             (\ v10 v11 v12 v13 v14 -> v14)
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v4) (coe v9))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v0) (coe v2))
                                             (coe
                                                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                (\ v10 v11 -> v11)
                                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe v0))
                                                v1 v2)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                   (coe d_'8804''45'isPreorder_2800))
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe v0) (coe v2)))
                                             erased)
                                          (d_'8854''45'mono'691''45''8805''45''8804'_4024
                                             (coe v4) (coe v5) (coe v9) (coe v8)))
                                       erased))
                          _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Integer.Properties.⊖-monoˡ-≤
d_'8854''45'mono'737''45''8804'_4056 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8854''45'mono'737''45''8804'_4056 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                0 -> coe
                       seq (coe v3)
                       (coe
                          d_'8804''45'refl_2728
                          (coe
                             MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                             (\ v5 ->
                                MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v5) (coe v0))
                             (\ v5 v6 -> v5) (0 :: Integer) (0 :: Integer)))
                _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                            -> coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                    (coe d_'8804''45'isPreorder_2800)
                                    (\ v7 v8 v9 -> coe du_'60''8658''8804'_2846 v9))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    (\ v7 ->
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                         (coe v7) (coe v0))
                                    (\ v7 v8 -> v7) (0 :: Integer) v2)
                                 (coe
                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                    (\ v7 v8 -> v8)
                                    (\ v7 ->
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                         (coe v7) (coe v0))
                                    (0 :: Integer) v2)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                       (coe d_'8804''45'isPreorder_2800)
                                       (\ v7 v8 v9 v10 v11 ->
                                          coe du_'8804''45''60''45'trans_2958 v10 v11))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                       (coe (0 :: Integer)) (coe v0))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                       (coe (0 :: Integer)) (coe v4))
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v7 v8 -> v8)
                                       (\ v7 ->
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                            (coe v7) (coe v0))
                                       (0 :: Integer) v2)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                          (coe d_'8804''45'isPreorder_2800)
                                          (\ v7 v8 v9 v10 v11 ->
                                             coe du_'8804''45''60''45'trans_2958 v10 v11))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe (0 :: Integer)) (coe v4))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v5) (coe v4))
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v7 v8 -> v8)
                                          (\ v7 ->
                                             MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                               (coe v7) (coe v0))
                                          (0 :: Integer) v2)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                          (\ v7 v8 v9 v10 v11 -> v11)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v5) (coe v4))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v2) (coe v0))
                                          (coe
                                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                             (\ v7 v8 -> v8)
                                             (\ v7 ->
                                                MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                  (coe v7) (coe v0))
                                             (0 :: Integer) v2)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe d_'8804''45'isPreorder_2800))
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v2) (coe v0)))
                                          erased)
                                       (d_'8854''45'mono'737''45''8804'_4056
                                          (coe v4) (coe (0 :: Integer)) (coe v5)
                                          (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                                    (d_'8854''45'mono'691''45''8805''45''8804'_4024
                                       (coe (0 :: Integer)) (coe v0) (coe v4)
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2844
                                          (coe v4))))
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                            -> let v9 = subInt (coe v1) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                       (coe d_'8804''45'isPreorder_2800)
                                       (\ v10 v11 v12 -> coe du_'60''8658''8804'_2846 v12))
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                       (\ v10 ->
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                            (coe v10) (coe v0))
                                       (\ v10 v11 -> v10) v1 v2)
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v10 v11 -> v11)
                                       (\ v10 ->
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                            (coe v10) (coe v0))
                                       v1 v2)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                       (\ v10 v11 v12 v13 v14 -> v14)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v1) (coe v0))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v9) (coe v4))
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v10 v11 -> v11)
                                          (\ v10 ->
                                             MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                               (coe v10) (coe v0))
                                          v1 v2)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                             (coe d_'8804''45'isPreorder_2800)
                                             (\ v10 v11 v12 v13 v14 ->
                                                coe du_'8804''45''60''45'trans_2958 v13 v14))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v9) (coe v4))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v5) (coe v4))
                                          (coe
                                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                             (\ v10 v11 -> v11)
                                             (\ v10 ->
                                                MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                  (coe v10) (coe v0))
                                             v1 v2)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                             (\ v10 v11 v12 v13 v14 -> v14)
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v5) (coe v4))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v2) (coe v0))
                                             (coe
                                                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                (\ v10 v11 -> v11)
                                                (\ v10 ->
                                                   MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                     (coe v10) (coe v0))
                                                v1 v2)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                   (coe d_'8804''45'isPreorder_2800))
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe v2) (coe v0)))
                                             erased)
                                          (d_'8854''45'mono'737''45''8804'_4056
                                             (coe v4) (coe v9) (coe v5) (coe v8)))
                                       erased))
                          _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Integer.Properties.⊖-monoʳ->-<
d_'8854''45'mono'691''45''62''45''60'_4086 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8854''45'mono'691''45''62''45''60'_4086 v0 v1 v2 v3
  = case coe v0 of
      0 -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> case coe v6 of
                    MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                      -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                      -> coe
                           MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                           (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v5 = subInt (coe v1) (coe (1 :: Integer)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                     -> case coe v8 of
                          MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                            -> let v10
                                     = coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0)
                                       (coe v1))
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                       (\ v11 v12 v13 v14 v15 -> v15)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v0) (coe v1))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v4) (coe v5))
                                       v0
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                             (\ v11 v12 v13 v14 v15 ->
                                                coe du_'60''45'trans_2986 v14 v15)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                             (\ v11 v12 v13 v14 v15 ->
                                                coe du_'60''45''8804''45'trans_2972 v14 v15))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v4) (coe v5))
                                          v0 v0
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe d_'8804''45'isPreorder_2800))
                                             (coe v0))
                                          (d_m'8854'n'60'1'43'm_3930 (coe v4) (coe v5)))
                                       erased))
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v11
                            -> let v12 = subInt (coe v2) (coe (1 :: Integer)) in
                               coe
                                 (let v13
                                        = coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                                  coe
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                       (coe v13)
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0)
                                          (coe v1))
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v0)
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                          (\ v14 v15 v16 v17 v18 -> v18)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v0) (coe v1))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v4) (coe subInt (coe v1) (coe (1 :: Integer))))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v0) (coe v2))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                                (\ v14 v15 v16 v17 v18 ->
                                                   coe du_'60''45'trans_2986 v17 v18)
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                                (\ v14 v15 v16 v17 v18 ->
                                                   coe du_'60''45''8804''45'trans_2972 v17 v18))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v4) (coe subInt (coe v1) (coe (1 :: Integer))))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v4) (coe v12))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v0) (coe v2))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                                (\ v14 v15 v16 v17 v18 -> v18)
                                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe v4) (coe v12))
                                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe v0) (coe v2))
                                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe v0) (coe v2))
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                      (coe d_'8804''45'isPreorder_2800))
                                                   (coe
                                                      MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                      (coe v0) (coe v2)))
                                                erased)
                                             (d_'8854''45'mono'691''45''62''45''60'_4086
                                                (coe v4) (coe subInt (coe v1) (coe (1 :: Integer)))
                                                (coe v12)
                                                (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v11)))
                                          erased)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Integer.Properties.⊖-monoˡ-<
d_'8854''45'mono'737''45''60'_4114 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8854''45'mono'737''45''60'_4114 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v3
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v5 = subInt (coe v2) (coe (1 :: Integer)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                     -> case coe v8 of
                          MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                            -> let v10
                                     = coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                    (coe v10) (coe subInt (coe (0 :: Integer)) (coe v0))
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v2)
                                       (coe v0))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                          (\ v11 v12 v13 v14 v15 ->
                                             coe du_'60''45'trans_2986 v14 v15)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                          (\ v11 v12 v13 v14 v15 ->
                                             coe du_'60''45''8804''45'trans_2972 v14 v15))
                                       (subInt (coe (0 :: Integer)) (coe v0))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v5) (coe v4))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v2) (coe v0))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                          (\ v11 v12 v13 v14 v15 -> v15)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v5) (coe v4))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v2) (coe v0))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v2) (coe v0))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe d_'8804''45'isPreorder_2800))
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v2) (coe v0)))
                                          erased)
                                       (d_'45'1'43'm'60'n'8854'm_3958 (coe v4) (coe v5))))
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v11
                            -> let v12 = subInt (coe v1) (coe (1 :: Integer)) in
                               coe
                                 (let v13
                                        = coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                                  coe
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                       (coe v13)
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v1)
                                          (coe v0))
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v2)
                                          (coe v0))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                          (\ v14 v15 v16 v17 v18 -> v18)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v1) (coe v0))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v12) (coe v4))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v2) (coe v0))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                                (\ v14 v15 v16 v17 v18 ->
                                                   coe du_'60''45'trans_2986 v17 v18)
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                                (\ v14 v15 v16 v17 v18 ->
                                                   coe du_'60''45''8804''45'trans_2972 v17 v18))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v12) (coe v4))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe subInt (coe v2) (coe (1 :: Integer))) (coe v4))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                (coe v2) (coe v0))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                                (\ v14 v15 v16 v17 v18 -> v18)
                                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe subInt (coe v2) (coe (1 :: Integer)))
                                                   (coe v4))
                                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe v2) (coe v0))
                                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                   (coe v2) (coe v0))
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                      (coe d_'8804''45'isPreorder_2800))
                                                   (coe
                                                      MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                                      (coe v2) (coe v0)))
                                                erased)
                                             (d_'8854''45'mono'737''45''60'_4114
                                                (coe v4) (coe v12)
                                                (coe subInt (coe v2) (coe (1 :: Integer)))
                                                (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v11)))
                                          erased)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Integer.Properties.+-comm
d_'43''45'comm_4138 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_4138 = erased
-- Data.Integer.Properties.+-identityˡ
d_'43''45'identity'737'_4148 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737'_4148 = erased
-- Data.Integer.Properties.+-identityʳ
d_'43''45'identity'691'_4150 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_4150 = erased
-- Data.Integer.Properties.+-identity
d_'43''45'identity_4152 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'identity_4152
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.distribˡ-⊖-+-pos
d_distrib'737''45''8854''45''43''45'pos_4160 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737''45''8854''45''43''45'pos_4160 = erased
-- Data.Integer.Properties.distribˡ-⊖-+-neg
d_distrib'737''45''8854''45''43''45'neg_4180 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737''45''8854''45''43''45'neg_4180 = erased
-- Data.Integer.Properties.distribʳ-⊖-+-pos
d_distrib'691''45''8854''45''43''45'pos_4200 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691''45''8854''45''43''45'pos_4200 = erased
-- Data.Integer.Properties.distribʳ-⊖-+-neg
d_distrib'691''45''8854''45''43''45'neg_4220 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691''45''8854''45''43''45'neg_4220 = erased
-- Data.Integer.Properties.+-assoc
d_'43''45'assoc_4234 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_4234 = erased
-- Data.Integer.Properties.+-inverseˡ
d_'43''45'inverse'737'_4414 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'737'_4414 = erased
-- Data.Integer.Properties.+-inverseʳ
d_'43''45'inverse'691'_4420 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'691'_4420 = erased
-- Data.Integer.Properties.+-inverse
d_'43''45'inverse_4422 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_4422
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.+-isMagma
d_'43''45'isMagma_4424 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'43''45'isMagma_4424
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Integer.Properties.+-isSemigroup
d_'43''45'isSemigroup_4426 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'43''45'isSemigroup_4426
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe d_'43''45'isMagma_4424) erased
-- Data.Integer.Properties.+-isCommutativeSemigroup
d_'43''45'isCommutativeSemigroup_4428 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'43''45'isCommutativeSemigroup_4428
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemigroup'46'constructor_12093
      (coe d_'43''45'isSemigroup_4426) erased
-- Data.Integer.Properties.+-0-isMonoid
d_'43''45'0'45'isMonoid_4430 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'0'45'isMonoid_4430
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe d_'43''45'isSemigroup_4426) (coe d_'43''45'identity_4152)
-- Data.Integer.Properties.+-0-isCommutativeMonoid
d_'43''45'0'45'isCommutativeMonoid_4432 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'0'45'isCommutativeMonoid_4432
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe d_'43''45'0'45'isMonoid_4430) erased
-- Data.Integer.Properties.+-0-isGroup
d_'43''45'0'45'isGroup_4434 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_'43''45'0'45'isGroup_4434
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsGroup'46'constructor_26963
      (coe d_'43''45'0'45'isMonoid_4430) (coe d_'43''45'inverse_4422)
      erased
-- Data.Integer.Properties.+-0-isAbelianGroup
d_'43''45'0'45'isAbelianGroup_4436 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'0'45'isAbelianGroup_4436
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsAbelianGroup'46'constructor_32441
      (coe d_'43''45'0'45'isGroup_4434) erased
-- Data.Integer.Properties.+-magma
d_'43''45'magma_4438 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'43''45'magma_4438
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1279
      MAlonzo.Code.Data.Integer.Base.d__'43'__276 d_'43''45'isMagma_4424
-- Data.Integer.Properties.+-semigroup
d_'43''45'semigroup_4440 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'43''45'semigroup_4440
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9793
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      d_'43''45'isSemigroup_4426
-- Data.Integer.Properties.+-commutativeSemigroup
d_'43''45'commutativeSemigroup_4442 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'43''45'commutativeSemigroup_4442
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemigroup'46'constructor_12035
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      d_'43''45'isCommutativeSemigroup_4428
-- Data.Integer.Properties.+-0-monoid
d_'43''45'0'45'monoid_4444 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'43''45'0'45'monoid_4444
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16157
      MAlonzo.Code.Data.Integer.Base.d__'43'__276 (0 :: Integer)
      d_'43''45'0'45'isMonoid_4430
-- Data.Integer.Properties.+-0-commutativeMonoid
d_'43''45'0'45'commutativeMonoid_4446 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'43''45'0'45'commutativeMonoid_4446
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17931
      MAlonzo.Code.Data.Integer.Base.d__'43'__276 (0 :: Integer)
      d_'43''45'0'45'isCommutativeMonoid_4432
-- Data.Integer.Properties.+-0-abelianGroup
d_'43''45'0'45'abelianGroup_4448 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636
d_'43''45'0'45'abelianGroup_4448
  = coe
      MAlonzo.Code.Algebra.Bundles.C_AbelianGroup'46'constructor_29855
      MAlonzo.Code.Data.Integer.Base.d__'43'__276 (0 :: Integer)
      MAlonzo.Code.Data.Integer.Base.d_'45'__252
      d_'43''45'0'45'isAbelianGroup_4436
-- Data.Integer.Properties.pos-+
d_pos'45''43'_4450 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pos'45''43'_4450 = erased
-- Data.Integer.Properties.neg-distrib-+
d_neg'45'distrib'45''43'_4462 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'45''43'_4462 = erased
-- Data.Integer.Properties.◃-distrib-+
d_'9667''45'distrib'45''43'_4490 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45'distrib'45''43'_4490 = erased
-- Data.Integer.Properties.+-monoʳ-≤
d_'43''45'mono'691''45''8804'_4510 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'mono'691''45''8804'_4510 v0 v1 v2 v3
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v3 of
            MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
              -> coe
                   d_'8854''45'mono'691''45''8805''45''8804'_4024 (coe v0)
                   (coe subInt (coe (0 :: Integer)) (coe v1))
                   (coe subInt (coe (0 :: Integer)) (coe v2))
                   (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
            MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
              -> coe
                   du_'8804''45'trans_2730
                   (coe
                      d_m'8854'n'8804'm_3912 (coe v0)
                      (coe subInt (coe (0 :: Integer)) (coe v1)))
                   (coe
                      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3482 (coe v0)))
            MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
              -> coe
                   MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''8804'_3554
                      (coe v0) (coe v2) (coe v6))
            _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v3 of
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
               -> let v7 = subInt (coe (-1 :: Integer)) (coe v1) in
                  coe
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''8804'_3554
                          (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v7) (coe v6)))
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
               -> coe
                    du_'8804''45'trans_2730
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3482
                          (coe subInt (coe (0 :: Integer)) (coe v0))))
                    (coe
                       d_'45'1'43'm'8804'n'8854'm_3992
                       (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v2))
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
               -> coe
                    d_'8854''45'mono'737''45''8804'_4056
                    (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1) (coe v2)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.+-monoˡ-≤
d_'43''45'mono'737''45''8804'_4540 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'mono'737''45''8804'_4540 v0 v1 v2
  = coe d_'43''45'mono'691''45''8804'_4510 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Properties.+-mono-≤
d_'43''45'mono'45''8804'_4556 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'mono'45''8804'_4556 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2800)
         (\ v6 v7 v8 -> coe du_'60''8658''8804'_2846 v8))
      (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v0) (coe v2))
      (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_2800)
            (\ v6 v7 v8 v9 v10 -> coe du_'8804''45''60''45'trans_2958 v9 v10))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v0) (coe v2))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v2))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_2800)
               (\ v6 v7 v8 v9 v10 -> coe du_'8804''45''60''45'trans_2958 v9 v10))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v2))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2800))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3)))
            (d_'43''45'mono'691''45''8804'_4510
               (coe v1) (coe v2) (coe v3) (coe v5)))
         (coe d_'43''45'mono'737''45''8804'_4540 v2 v0 v1 v4))
-- Data.Integer.Properties.i≤j⇒i≤k+j
d_i'8804'j'8658'i'8804'k'43'j_4578 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'i'8804'k'43'j_4578 v0 v1 v2 ~v3 v4
  = du_i'8804'j'8658'i'8804'k'43'j_4578 v0 v1 v2 v4
du_i'8804'j'8658'i'8804'k'43'j_4578 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'j'8658'i'8804'k'43'j_4578 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''8804'_4556 (coe (0 :: Integer)) (coe v2)
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe v3)
-- Data.Integer.Properties.i≤j+i
d_i'8804'j'43'i_4592 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'43'i_4592 v0 v1 ~v2 = du_i'8804'j'43'i_4592 v0 v1
du_i'8804'j'43'i_4592 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'j'43'i_4592 v0 v1
  = coe
      du_i'8804'j'8658'i'8804'k'43'j_4578 (coe v0) (coe v0) (coe v1)
      (coe d_'8804''45'refl_2728 (coe v0))
-- Data.Integer.Properties.i≤i+j
d_i'8804'i'43'j_4604 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'i'43'j_4604 v0 v1 ~v2 = du_i'8804'i'43'j_4604 v0 v1
du_i'8804'i'43'j_4604 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'i'43'j_4604 v0 v1
  = coe du_i'8804'j'43'i_4592 (coe v0) (coe v1)
-- Data.Integer.Properties.+-monoʳ-<
d_'43''45'mono'691''45''60'_4616 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'691''45''60'_4616 v0 v1 v2 v3
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v3 of
            MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v6
              -> coe
                   d_'8854''45'mono'691''45''62''45''60'_4086 (coe v0)
                   (coe subInt (coe (0 :: Integer)) (coe v1))
                   (coe subInt (coe (0 :: Integer)) (coe v2))
                   (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
            MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
              -> coe
                   du_'60''45''8804''45'trans_2972
                   (coe
                      du_m'8854'1'43'n'60'm_3942 (coe v0)
                      (coe subInt (coe (0 :: Integer)) (coe v1)))
                   (coe
                      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3482 (coe v0)))
            MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v6
              -> coe
                   MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3596
                      (coe v0) (coe v6))
            _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v4 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v3 of
                MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v7
                  -> coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3596
                          (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v7))
                MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
                  -> coe
                       du_'60''45''8804''45'trans_2972
                       (coe
                          MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3482
                             (coe subInt (coe (0 :: Integer)) (coe v0))))
                       (coe
                          d_'45''91'1'43'm'93''8804'n'8854'm'43'1_3976 (coe v4) (coe v2))
                MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v7
                  -> coe
                       d_'8854''45'mono'737''45''60'_4114
                       (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1) (coe v2)
                       (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Integer.Properties.+-monoˡ-<
d_'43''45'mono'737''45''60'_4644 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'737''45''60'_4644 v0 v1 v2
  = coe d_'43''45'mono'691''45''60'_4616 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Properties.+-mono-<
d_'43''45'mono'45''60'_4660 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'45''60'_4660 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v6)
         (coe MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v0) (coe v2))
         (coe MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (\ v7 v8 v9 v10 v11 -> coe du_'60''45'trans_2986 v10 v11)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (\ v7 v8 v9 v10 v11 ->
                  coe du_'60''45''8804''45'trans_2972 v10 v11))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v0) (coe v2))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v2))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (\ v7 v8 v9 v10 v11 -> coe du_'60''45'trans_2986 v10 v11)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (\ v7 v8 v9 v10 v11 ->
                     coe du_'60''45''8804''45'trans_2972 v10 v11))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v2))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_2800))
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'43'__276 (coe v1) (coe v3)))
               (d_'43''45'mono'691''45''60'_4616
                  (coe v1) (coe v2) (coe v3) (coe v5)))
            (coe d_'43''45'mono'737''45''60'_4644 v2 v0 v1 v4)))
-- Data.Integer.Properties.+-mono-≤-<
d_'43''45'mono'45''8804''45''60'_4678 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'45''8804''45''60'_4678 v0 v1 v2 v3 v4 v5
  = coe
      du_'8804''45''60''45'trans_2958
      (coe d_'43''45'mono'737''45''8804'_4540 v2 v0 v1 v4)
      (coe
         d_'43''45'mono'691''45''60'_4616 (coe v1) (coe v2) (coe v3)
         (coe v5))
-- Data.Integer.Properties.+-mono-<-≤
d_'43''45'mono'45''60''45''8804'_4690 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'45''60''45''8804'_4690 v0 v1 v2 v3 v4 v5
  = coe
      du_'60''45''8804''45'trans_2972
      (coe d_'43''45'mono'737''45''60'_4644 v2 v0 v1 v4)
      (coe
         d_'43''45'mono'691''45''8804'_4510 (coe v1) (coe v2) (coe v3)
         (coe v5))
-- Data.Integer.Properties.neg-minus-pos
d_neg'45'minus'45'pos_4706 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'minus'45'pos_4706 = erased
-- Data.Integer.Properties.+-minus-telescope
d_'43''45'minus'45'telescope_4722 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'minus'45'telescope_4722 = erased
-- Data.Integer.Properties.[+m]-[+n]≡m⊖n
d_'91''43'm'93''45''91''43'n'93''8801'm'8854'n_4744 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91''43'm'93''45''91''43'n'93''8801'm'8854'n_4744 = erased
-- Data.Integer.Properties.∣i-j∣≡∣j-i∣
d_'8739'i'45'j'8739''8801''8739'j'45'i'8739'_4758 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'i'45'j'8739''8801''8739'j'45'i'8739'_4758 = erased
-- Data.Integer.Properties.∣-∣-≤
d_'8739''45''8739''45''8804'_4788 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''45''8804'_4788 = erased
-- Data.Integer.Properties.i≡j⇒i-j≡0
d_i'8801'j'8658'i'45'j'8801'0_4826 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8801'j'8658'i'45'j'8801'0_4826 = erased
-- Data.Integer.Properties.i-j≡0⇒i≡j
d_i'45'j'8801'0'8658'i'8801'j_4834 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'45'j'8801'0'8658'i'8801'j_4834 = erased
-- Data.Integer.Properties.i≤j⇒i-k≤j
d_i'8804'j'8658'i'45'k'8804'j_4852 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'i'45'k'8804'j_4852 v0 ~v1 v2 ~v3 v4
  = du_i'8804'j'8658'i'45'k'8804'j_4852 v0 v2 v4
du_i'8804'j'8658'i'45'k'8804'j_4852 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'j'8658'i'45'k'8804'j_4852 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
                    coe
                      du_'8804''45'trans_2730
                      (coe d_m'8854'n'8804'm_3912 (coe v0) (coe v1)) (coe v2)
                _ -> let v4 = subInt (coe (-1 :: Integer)) (coe v0) in
                     coe
                       (coe
                          du_'8804''45'trans_2730
                          (coe
                             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3482 (coe v4))
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2844
                                   (coe addInt (coe v4) (coe v3)))))
                          (coe v2)))
-- Data.Integer.Properties.i-j≤i
d_i'45'j'8804'i_4880 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'45'j'8804'i_4880 v0 v1 ~v2 = du_i'45'j'8804'i_4880 v0 v1
du_i'45'j'8804'i_4880 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'45'j'8804'i_4880 v0 v1
  = coe
      du_i'8804'j'8658'i'45'k'8804'j_4852 (coe v0) (coe v1)
      (coe d_'8804''45'refl_2728 (coe v0))
-- Data.Integer.Properties.i≤j⇒i-j≤0
d_i'8804'j'8658'i'45'j'8804'0_4886 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'i'45'j'8804'0_4886 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v5
        -> let v6 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (let v7 = subInt (coe (-1 :: Integer)) (coe v1) in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                      (coe d_'8804''45'isPreorder_2800)
                      (\ v8 v9 v10 -> coe du_'60''8658''8804'_2846 v10))
                   (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1))
                   MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                      (\ v8 v9 v10 v11 v12 -> v12)
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                         (coe subInt (coe (0 :: Integer)) (coe v1))
                         (coe subInt (coe (0 :: Integer)) (coe v0)))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v7) (coe v6))
                      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe d_'8804''45'isPreorder_2800)
                            (\ v8 v9 v10 v11 v12 ->
                               coe du_'8804''45''60''45'trans_2958 v11 v12))
                         (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v7) (coe v6))
                         (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v7) (coe v7))
                         MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                            (\ v8 v9 v10 v11 v12 -> v12)
                            (MAlonzo.Code.Data.Integer.Base.d__'8854'__258 (coe v7) (coe v7))
                            MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                            MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                  (coe d_'8804''45'isPreorder_2800))
                               (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
                            erased)
                         (d_'8854''45'mono'691''45''8805''45''8804'_4024
                            (coe v7) (coe v6) (coe v7) (coe v5)))
                      erased)))
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe
             du_i'8804'j'8658'i'45'k'8804'j_4852 (coe v0) (coe v1)
             (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40)
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
        -> case coe v1 of
             0 -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
             _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                         -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                         -> let v10 = subInt (coe v0) (coe (1 :: Integer)) in
                            coe
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                    (coe d_'8804''45'isPreorder_2800)
                                    (\ v11 v12 v13 -> coe du_'60''8658''8804'_2846 v13))
                                 (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1))
                                 MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                    (\ v11 v12 v13 v14 v15 -> v15)
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                       (coe v0) (coe v1))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                       (coe v10) (coe v6))
                                    MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                          (coe d_'8804''45'isPreorder_2800)
                                          (\ v11 v12 v13 v14 v15 ->
                                             coe du_'8804''45''60''45'trans_2958 v14 v15))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v10) (coe v6))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                          (coe v10) (coe v10))
                                       MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                          (\ v11 v12 v13 v14 v15 -> v15)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                                             (coe v10) (coe v10))
                                          MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                          MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe d_'8804''45'isPreorder_2800))
                                             (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
                                          erased)
                                       (d_'8854''45'mono'691''45''8805''45''8804'_4024
                                          (coe v10) (coe v6) (coe v10) (coe v9)))
                                    erased))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.i-j≤0⇒i≤j
d_i'45'j'8804'0'8658'i'8804'j_4912 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'45'j'8804'0'8658'i'8804'j_4912 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2800)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_2846 v5))
      v0 v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
         (\ v3 v4 v5 v6 v7 -> v7) v0
         (MAlonzo.Code.Data.Integer.Base.d__'43'__276
            (coe v0) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
            (\ v3 v4 v5 v6 v7 -> v7)
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276
               (coe v0) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276
               (coe v0)
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'43'__276
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1))
                  (coe v1)))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
               (\ v3 v4 v5 v6 v7 -> v7)
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                  (coe v0)
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1))
                     (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                  (coe MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1))
                  (coe v1))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                     (coe d_'8804''45'isPreorder_2800)
                     (\ v3 v4 v5 v6 v7 -> coe du_'8804''45''60''45'trans_2958 v6 v7))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1))
                     (coe v1))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
                  v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v3 v4 v5 v6 v7 -> v7)
                     (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                        (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
                     v1 v1
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_2800))
                        (coe v1))
                     erased)
                  (coe
                     d_'43''45'mono'737''45''8804'_4540 v1
                     (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1))
                     MAlonzo.Code.Data.Integer.Base.d_0ℤ_12 v2))
               erased)
            erased)
         erased)
-- Data.Integer.Properties.i≤j⇒0≤j-i
d_i'8804'j'8658'0'8804'j'45'i_4924 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'0'8804'j'45'i_4924 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2800)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_2846 v5))
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v1) (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
         (\ v3 v4 v5 v6 v7 -> v7) MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
         (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v0))
         (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v1) (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_2800)
               (\ v3 v4 v5 v6 v7 -> coe du_'8804''45''60''45'trans_2958 v6 v7))
            (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v0))
            (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v1) (coe v0))
            (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v1) (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2800))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v1) (coe v0)))
            (coe
               d_'43''45'mono'737''45''8804'_4540
               (MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0)) v0 v1 v2))
         erased)
-- Data.Integer.Properties.0≤i-j⇒j≤i
d_0'8804'i'45'j'8658'j'8804'i_4936 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_0'8804'i'45'j'8658'j'8804'i_4936 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2800)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_2846 v5))
      v1 v0
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
         (\ v3 v4 v5 v6 v7 -> v7) v1
         (MAlonzo.Code.Data.Integer.Base.d__'43'__276
            (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
         v0
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_2800)
               (\ v3 v4 v5 v6 v7 -> coe du_'8804''45''60''45'trans_2958 v6 v7))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276
               (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__276
               (coe MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1))
               (coe v1))
            v0
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v3 v4 v5 v6 v7 -> v7)
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                  (coe MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1))
                  (coe v1))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                  (coe v0)
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1))
                     (coe v1)))
               v0
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe v0)
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'43'__276
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1))
                        (coe v1)))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe v0) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
                  v0
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v3 v4 v5 v6 v7 -> v7)
                     (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                        (coe v0) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
                     v0 v0
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_2800))
                        (coe v0))
                     erased)
                  erased)
               erased)
            (coe
               d_'43''45'mono'737''45''8804'_4540 v1
               MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
               (MAlonzo.Code.Data.Integer.Base.d__'45'__294 (coe v0) (coe v1))
               v2))
         erased)
-- Data.Integer.Properties.i≤j⇒i≤1+j
d_i'8804'j'8658'i'8804'1'43'j_4948 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'i'8804'1'43'j_4948 v0 v1
  = coe
      du_i'8804'j'8658'i'8804'k'43'j_4578 (coe v0) (coe v1)
      (coe (1 :: Integer))
-- Data.Integer.Properties.i≤suc[i]
d_i'8804'suc'91'i'93'_4952 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'suc'91'i'93'_4952 v0
  = coe du_i'8804'j'43'i_4592 (coe v0) (coe (1 :: Integer))
-- Data.Integer.Properties.suc-+
d_suc'45''43'_4960 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45''43'_4960 = erased
-- Data.Integer.Properties.i≢suc[i]
d_i'8802'suc'91'i'93'_4970 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_i'8802'suc'91'i'93'_4970 = erased
-- Data.Integer.Properties.1-[1+n]≡-n
d_1'45''91'1'43'n'93''8801''45'n_4976 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'45''91'1'43'n'93''8801''45'n_4976 = erased
-- Data.Integer.Properties.suc-mono
d_suc'45'mono_4980 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_suc'45'mono_4980 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v5
        -> coe
             d_'8854''45'mono'691''45''8805''45''8804'_4024 (coe (1 :: Integer))
             (coe subInt (coe (0 :: Integer)) (coe v0))
             (coe subInt (coe (0 :: Integer)) (coe v1))
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> let v5 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe d_'8804''45'isPreorder_2800)
                   (\ v6 v7 v8 -> coe du_'60''8658''8804'_2846 v8))
                (coe
                   MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                   MAlonzo.Code.Data.Integer.Base.d_suc_300 (\ v6 v7 -> v6) v0 v1)
                (coe
                   MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                   (\ v6 v7 -> v7) MAlonzo.Code.Data.Integer.Base.d_suc_300 v0 v1)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                   (\ v6 v7 v8 v9 v10 -> v10)
                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                      (coe (1 :: Integer)) (coe subInt (coe (0 :: Integer)) (coe v0)))
                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                      (coe (0 :: Integer)) (coe v5))
                   (coe
                      MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                      (\ v6 v7 -> v7) MAlonzo.Code.Data.Integer.Base.d_suc_300 v0 v1)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe d_'8804''45'isPreorder_2800)
                         (\ v6 v7 v8 v9 v10 -> coe du_'8804''45''60''45'trans_2958 v9 v10))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__258
                         (coe (0 :: Integer)) (coe v5))
                      (MAlonzo.Code.Data.Integer.Base.d_suc_300 (coe v1))
                      (coe
                         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                         (\ v6 v7 -> v7) MAlonzo.Code.Data.Integer.Base.d_suc_300 v0 v1)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe d_'8804''45'isPreorder_2800))
                         (coe MAlonzo.Code.Data.Integer.Base.d_suc_300 (coe v1)))
                      (coe du_0'8854'm'8804''43'_4002 (coe v5)))
                   erased))
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.suc[i]≤j⇒i<j
d_suc'91'i'93''8804'j'8658'i'60'j_4994 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_suc'91'i'93''8804'j'8658'i'60'j_4994 v0 v1 v2
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v2 of
            MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
              -> coe MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v5
            _ -> MAlonzo.RTE.mazUnreachableError
      -1 -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe
                   seq (coe v2) (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
             _ -> case coe v2 of
                    MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v5
                      -> coe
                           MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                           (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.i<j⇒suc[i]≤j
d_i'60'j'8658'suc'91'i'93''8804'j_5014 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'60'j'8658'suc'91'i'93''8804'j_5014 v0 v1 v2
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v2 of
            MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v5
              -> coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
            _ -> MAlonzo.RTE.mazUnreachableError
      -1
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe
                   seq (coe v2)
                   (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40)
             _ -> case coe v2 of
                    MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v5
                      -> coe
                           MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                           (coe MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.suc-pred
d_suc'45'pred_5026 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'pred_5026 = erased
-- Data.Integer.Properties.pred-suc
d_pred'45'suc_5036 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'45'suc_5036 = erased
-- Data.Integer.Properties.+-pred
d_'43''45'pred_5048 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'pred_5048 = erased
-- Data.Integer.Properties.pred-+
d_pred'45''43'_5064 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'45''43'_5064 = erased
-- Data.Integer.Properties.neg-suc
d_neg'45'suc_5076 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'suc_5076 = erased
-- Data.Integer.Properties.minus-suc
d_minus'45'suc_5084 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_minus'45'suc_5084 = erased
-- Data.Integer.Properties.i≤pred[j]⇒i<j
d_i'8804'pred'91'j'93''8658'i'60'j_5094 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_i'8804'pred'91'j'93''8658'i'60'j_5094 ~v0 v1 v2
  = du_i'8804'pred'91'j'93''8658'i'60'j_5094 v1 v2
du_i'8804'pred'91'j'93''8658'i'60'j_5094 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_i'8804'pred'91'j'93''8658'i'60'j_5094 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            du_'8804''45''60''45'trans_2958 (coe v1)
            (coe du_m'8854'1'43'n'60'm_3942 (coe v0) (coe (1 :: Integer)))
      _ -> coe
             du_'8804''45''60''45'trans_2958 (coe v1)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                   (coe subInt (coe (0 :: Integer)) (coe v0))))
-- Data.Integer.Properties.i<j⇒i≤pred[j]
d_i'60'j'8658'i'8804'pred'91'j'93'_5104 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'60'j'8658'i'8804'pred'91'j'93'_5104 ~v0 v1 v2
  = du_i'60'j'8658'i'8804'pred'91'j'93'_5104 v1 v2
du_i'60'j'8658'i'8804'pred'91'j'93'_5104 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'60'j'8658'i'8804'pred'91'j'93'_5104 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          case coe v1 of
            MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
              -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
            MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v4
              -> coe
                   MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                   (coe MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v4))
            _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v4
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v4
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.i≤j⇒pred[i]≤j
d_i'8804'j'8658'pred'91'i'93''8804'j_5116 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'pred'91'i'93''8804'j_5116 ~v0 ~v1 v2
  = du_i'8804'j'8658'pred'91'i'93''8804'j_5116 v2
du_i'8804'j'8658'pred'91'i'93''8804'j_5116 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'j'8658'pred'91'i'93''8804'j_5116 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v3
        -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v3
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.pred-mono
d_pred'45'mono_5122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_pred'45'mono_5122 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v5
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                    (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
        -> coe
             d_'8854''45'mono'737''45''8804'_4056 (coe (1 :: Integer)) (coe v0)
             (coe v1) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.*-comm
d_'42''45'comm_5130 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_5130 = erased
-- Data.Integer.Properties.*-identityˡ
d_'42''45'identity'737'_5164 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_5164 = erased
-- Data.Integer.Properties.*-identityʳ
d_'42''45'identity'691'_5178 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_5178 = erased
-- Data.Integer.Properties.*-identity
d_'42''45'identity_5180 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_5180
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.*-zeroˡ
d_'42''45'zero'737'_5182 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'737'_5182 = erased
-- Data.Integer.Properties.*-zeroʳ
d_'42''45'zero'691'_5184 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'691'_5184 = erased
-- Data.Integer.Properties.*-zero
d_'42''45'zero_5186 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'zero_5186
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.*-assoc
d_'42''45'assoc_5188 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_5188 = erased
-- Data.Integer.Properties.distrib-lemma
d_distrib'45'lemma_5266 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'45'lemma_5266 = erased
-- Data.Integer.Properties.*-distribʳ-+
d_'42''45'distrib'691''45''43'_5342 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''43'_5342 = erased
-- Data.Integer.Properties.*-distribˡ-+
d_'42''45'distrib'737''45''43'_5608 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''43'_5608 = erased
-- Data.Integer.Properties.*-distrib-+
d_'42''45'distrib'45''43'_5610 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''43'_5610
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.*-isMagma
d_'42''45'isMagma_5612 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_5612
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Integer.Properties.*-isSemigroup
d_'42''45'isSemigroup_5614 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'42''45'isSemigroup_5614
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe d_'42''45'isMagma_5612) erased
-- Data.Integer.Properties.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_5616 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'42''45'isCommutativeSemigroup_5616
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemigroup'46'constructor_12093
      (coe d_'42''45'isSemigroup_5614) erased
-- Data.Integer.Properties.*-1-isMonoid
d_'42''45'1'45'isMonoid_5618 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'42''45'1'45'isMonoid_5618
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe d_'42''45'isSemigroup_5614) (coe d_'42''45'identity_5180)
-- Data.Integer.Properties.*-1-isCommutativeMonoid
d_'42''45'1'45'isCommutativeMonoid_5620 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'42''45'1'45'isCommutativeMonoid_5620
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe d_'42''45'1'45'isMonoid_5618) erased
-- Data.Integer.Properties.+-*-isSemiring
d_'43''45''42''45'isSemiring_5622 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_'43''45''42''45'isSemiring_5622
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_48071
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811
         (coe d_'43''45'0'45'isCommutativeMonoid_4432) erased erased
         (coe d_'42''45'identity_5180) (coe d_'42''45'distrib'45''43'_5610))
      (coe d_'42''45'zero_5186)
-- Data.Integer.Properties.+-*-isCommutativeSemiring
d_'43''45''42''45'isCommutativeSemiring_5624 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'43''45''42''45'isCommutativeSemiring_5624
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51895
      (coe d_'43''45''42''45'isSemiring_5622) erased
-- Data.Integer.Properties.+-*-isRing
d_'43''45''42''45'isRing_5626 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_'43''45''42''45'isRing_5626
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsRing'46'constructor_95033
      (coe d_'43''45'0'45'isAbelianGroup_4436) erased erased
      (coe d_'42''45'identity_5180) (coe d_'42''45'distrib'45''43'_5610)
-- Data.Integer.Properties.+-*-isCommutativeRing
d_'43''45''42''45'isCommutativeRing_5628 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796
d_'43''45''42''45'isCommutativeRing_5628
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeRing'46'constructor_100945
      (coe d_'43''45''42''45'isRing_5626) erased
-- Data.Integer.Properties.*-magma
d_'42''45'magma_5630 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'42''45'magma_5630
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1279
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 d_'42''45'isMagma_5612
-- Data.Integer.Properties.*-semigroup
d_'42''45'semigroup_5632 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'42''45'semigroup_5632
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9793
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      d_'42''45'isSemigroup_5614
-- Data.Integer.Properties.*-commutativeSemigroup
d_'42''45'commutativeSemigroup_5634 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'42''45'commutativeSemigroup_5634
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemigroup'46'constructor_12035
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      d_'42''45'isCommutativeSemigroup_5616
-- Data.Integer.Properties.*-1-monoid
d_'42''45'1'45'monoid_5636 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'42''45'1'45'monoid_5636
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16157
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16 d_'42''45'1'45'isMonoid_5618
-- Data.Integer.Properties.*-1-commutativeMonoid
d_'42''45'1'45'commutativeMonoid_5638 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'42''45'1'45'commutativeMonoid_5638
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17931
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'42''45'1'45'isCommutativeMonoid_5620
-- Data.Integer.Properties.+-*-semiring
d_'43''45''42''45'semiring_5640 ::
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2280
d_'43''45''42''45'semiring_5640
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semiring'46'constructor_41765
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'43''45''42''45'isSemiring_5622
-- Data.Integer.Properties.+-*-commutativeSemiring
d_'43''45''42''45'commutativeSemiring_5642 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'43''45''42''45'commutativeSemiring_5642
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_44731
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'43''45''42''45'isCommutativeSemiring_5624
-- Data.Integer.Properties.+-*-ring
d_'43''45''42''45'ring_5644 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3800
d_'43''45''42''45'ring_5644
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Ring'46'constructor_68489
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      MAlonzo.Code.Data.Integer.Base.d_'45'__252
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'43''45''42''45'isRing_5626
-- Data.Integer.Properties.+-*-commutativeRing
d_'43''45''42''45'commutativeRing_5646 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4016
d_'43''45''42''45'commutativeRing_5646
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeRing'46'constructor_72553
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      MAlonzo.Code.Data.Integer.Base.d_'45'__252
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'43''45''42''45'isCommutativeRing_5628
-- Data.Integer.Properties.abs-*
d_abs'45''42'_5648 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45''42'_5648 = erased
-- Data.Integer.Properties.sign-*
d_sign'45''42'_5658 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45''42'_5658 = erased
-- Data.Integer.Properties.*-cancelʳ-≡
d_'42''45'cancel'691''45''8801'_5676 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'691''45''8801'_5676 = erased
-- Data.Integer.Properties.*-cancelˡ-≡
d_'42''45'cancel'737''45''8801'_5720 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45''8801'_5720 = erased
-- Data.Integer.Properties.suc-*
d_suc'45''42'_5740 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45''42'_5740 = erased
-- Data.Integer.Properties.*-suc
d_'42''45'suc_5756 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'suc_5756 = erased
-- Data.Integer.Properties.-1*i≡-i
d_'45'1'42'i'8801''45'i_5770 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45'1'42'i'8801''45'i_5770 = erased
-- Data.Integer.Properties.i*j≡0⇒i≡0∨j≡0
d_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5780 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5780 v0 ~v1 ~v2
  = du_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5780 v0
du_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5780 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5780 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3822
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
-- Data.Integer.Properties.i*j≢0
d_i'42'j'8802'0_5810 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_i'42'j'8802'0_5810 ~v0 ~v1 ~v2 ~v3 = du_i'42'j'8802'0_5810
du_i'42'j'8802'0_5810 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_i'42'j'8802'0_5810
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0_3840
-- Data.Integer.Properties.^-identityʳ
d_'94''45'identity'691'_5822 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'identity'691'_5822 = erased
-- Data.Integer.Properties.^-zeroˡ
d_'94''45'zero'737'_5826 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'zero'737'_5826 = erased
-- Data.Integer.Properties.^-distribˡ-+-*
d_'94''45'distrib'737''45''43''45''42'_5840 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'distrib'737''45''43''45''42'_5840 = erased
-- Data.Integer.Properties.^-isMagmaHomomorphism
d_'94''45'isMagmaHomomorphism_5862 ::
  Integer ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_176
d_'94''45'isMagmaHomomorphism_5862 ~v0
  = du_'94''45'isMagmaHomomorphism_5862
du_'94''45'isMagmaHomomorphism_5862 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_176
du_'94''45'isMagmaHomomorphism_5862
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMagmaHomomorphism'46'constructor_4629
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsRelHomomorphism'46'constructor_587
         erased)
      erased
-- Data.Integer.Properties.^-isMonoidHomomorphism
d_'94''45'isMonoidHomomorphism_5872 ::
  Integer ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_350
d_'94''45'isMonoidHomomorphism_5872 ~v0
  = du_'94''45'isMonoidHomomorphism_5872
du_'94''45'isMonoidHomomorphism_5872 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_350
du_'94''45'isMonoidHomomorphism_5872
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidHomomorphism'46'constructor_9411
      (coe du_'94''45'isMagmaHomomorphism_5862) erased
-- Data.Integer.Properties.^-*-assoc
d_'94''45''42''45'assoc_5882 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45''42''45'assoc_5882 = erased
-- Data.Integer.Properties.i^n≡0⇒i≡0
d_i'94'n'8801'0'8658'i'8801'0_5908 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'94'n'8801'0'8658'i'8801'0_5908 = erased
-- Data.Integer.Properties.pos-*
d_pos'45''42'_5916 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pos'45''42'_5916 = erased
-- Data.Integer.Properties.neg-distribˡ-*
d_neg'45'distrib'737''45''42'_5930 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'737''45''42'_5930 = erased
-- Data.Integer.Properties.neg-distribʳ-*
d_neg'45'distrib'691''45''42'_5946 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'691''45''42'_5946 = erased
-- Data.Integer.Properties.◃-distrib-*
d_'9667''45'distrib'45''42'_5964 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45'distrib'45''42'_5964 = erased
-- Data.Integer.Properties.*-cancelʳ-≤-pos
d_'42''45'cancel'691''45''8804''45'pos_5998 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'cancel'691''45''8804''45'pos_5998 v0 v1 ~v2 ~v3 v4
  = du_'42''45'cancel'691''45''8804''45'pos_5998 v0 v1 v4
du_'42''45'cancel'691''45''8804''45'pos_5998 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'cancel'691''45''8804''45'pos_5998 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          coe
            seq (coe v2)
            (coe
               MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
               (coe
                  MAlonzo.Code.Data.Nat.Properties.du_'42''45'cancel'691''45''8804'_4030
                  (coe v0)))
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
             _ -> coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                       (coe
                          MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_'42''45'cancel'691''45''8804'_4030
                             (coe subInt (coe (0 :: Integer)) (coe v1)))))
-- Data.Integer.Properties.*-cancelˡ-≤-pos
d_'42''45'cancel'737''45''8804''45'pos_6032 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'cancel'737''45''8804''45'pos_6032 v0 v1 ~v2 ~v3
  = du_'42''45'cancel'737''45''8804''45'pos_6032 v0 v1
du_'42''45'cancel'737''45''8804''45'pos_6032 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'cancel'737''45''8804''45'pos_6032 v0 v1
  = coe
      du_'42''45'cancel'691''45''8804''45'pos_5998 (coe v0) (coe v1)
-- Data.Integer.Properties.*-monoʳ-≤-nonNeg
d_'42''45'mono'691''45''8804''45'nonNeg_6054 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'nonNeg_6054 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'691''45''8804''45'nonNeg_6054 v0 v2 v3 v4
du_'42''45'mono'691''45''8804''45'nonNeg_6054 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'mono'691''45''8804''45'nonNeg_6054 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> case coe v3 of
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                    (coe
                       MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'45''8804'_4060
                          (coe subInt (coe (0 :: Integer)) (coe v1)) (coe v0)
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776 (coe v0))))
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
               -> case coe v1 of
                    0 -> case coe v2 of
                           0 -> coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
                           _ -> coe
                                  MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                                  (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                    _ -> coe
                           MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''8804'_4070
                              (coe v0) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.*-monoˡ-≤-nonNeg
d_'42''45'mono'737''45''8804''45'nonNeg_6096 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'nonNeg_6096 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804''45'nonNeg_6096 v0 v2 v3
du_'42''45'mono'737''45''8804''45'nonNeg_6096 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'mono'737''45''8804''45'nonNeg_6096 v0 v1 v2
  = coe
      du_'42''45'mono'691''45''8804''45'nonNeg_6054 (coe v0) (coe v1)
      (coe v2)
-- Data.Integer.Properties.*-cancelˡ-≤-neg
d_'42''45'cancel'737''45''8804''45'neg_6120 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'cancel'737''45''8804''45'neg_6120 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''8804''45'neg_6120 v0 v1 v2 v4
du_'42''45'cancel'737''45''8804''45'neg_6120 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'cancel'737''45''8804''45'neg_6120 v0 v1 v2 v3
  = coe
      d_neg'45'cancel'45''8804'_3278 (coe v1) (coe v2)
      (coe
         du_'42''45'cancel'737''45''8804''45'pos_6032
         (MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1))
         (MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe d_'8804''45'isPreorder_2800)
               (\ v4 v5 v6 -> coe du_'60''8658''8804'_2846 v6))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
               (\ v4 v5 v6 v7 v8 -> v8)
               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                     (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v4 v5 v6 v7 v8 -> v8)
                  (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                        (coe v1)))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                        (coe d_'8804''45'isPreorder_2800)
                        (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_2958 v7 v8))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                        (\ v4 v5 v6 v7 v8 -> v8)
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2))
                        (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                           (coe
                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                              (coe v2)))
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                           (\ v4 v5 v6 v7 v8 -> v8)
                           (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                              (coe
                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                                 (coe v2)))
                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                 (coe d_'8804''45'isPreorder_2800))
                              (coe
                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))))
                           erased)
                        erased)
                     v3)
                  erased)
               erased)))
-- Data.Integer.Properties.*-cancelʳ-≤-neg
d_'42''45'cancel'691''45''8804''45'neg_6142 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'cancel'691''45''8804''45'neg_6142 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''8804''45'neg_6142 v0 v1 v2
du_'42''45'cancel'691''45''8804''45'neg_6142 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'cancel'691''45''8804''45'neg_6142 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''8804''45'neg_6120 (coe v2) (coe v0)
      (coe v1)
-- Data.Integer.Properties.*-monoˡ-≤-nonPos
d_'42''45'mono'737''45''8804''45'nonPos_6164 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'nonPos_6164 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''8804''45'nonPos_6164 v0 v2 v3 v4
du_'42''45'mono'737''45''8804''45'nonPos_6164 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'mono'737''45''8804''45'nonPos_6164 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                (coe d_'8804''45'isPreorder_2800)
                (\ v4 v5 v6 -> coe du_'60''8658''8804'_2846 v6))
             (coe
                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                (\ v4 v5 -> v5)
                (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0)) v1 v2)
             (coe
                MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0))
                (\ v4 v5 -> v4) v1 v2)
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                (\ v4 v5 v6 v7 v8 -> v8)
                (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2))
                (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                      (coe v2)))
                (coe
                   MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0))
                   (\ v4 v5 -> v4) v1 v2)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                   (\ v4 v5 v6 v7 v8 -> v8)
                   (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                         (coe v2)))
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
                   (coe
                      MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0))
                      (\ v4 v5 -> v4) v1 v2)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe d_'8804''45'isPreorder_2800)
                         (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_2958 v7 v8))
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                      (coe
                         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0))
                         (\ v4 v5 -> v4) v1 v2)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                         (\ v4 v5 v6 v7 v8 -> v8)
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                            (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                            (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                         (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                               (coe v1)))
                         (coe
                            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0))
                            (\ v4 v5 -> v4) v1 v2)
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                            (\ v4 v5 v6 v7 v8 -> v8)
                            (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                                  (coe v1)))
                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
                            (coe
                               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0))
                               (\ v4 v5 -> v4) v1 v2)
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                  (coe d_'8804''45'isPreorder_2800))
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1)))
                            erased)
                         erased)
                      (coe
                         du_'42''45'mono'737''45''8804''45'nonNeg_6096
                         (MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                         (coe
                            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                            (\ v4 v5 -> v5) MAlonzo.Code.Data.Integer.Base.d_'45'__252 v1 v2)
                         (coe
                            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                            MAlonzo.Code.Data.Integer.Base.d_'45'__252 (\ v4 v5 -> v4) v1 v2)
                         (coe du_neg'45'mono'45''8804'_3272 (coe v2) (coe v3))))
                   erased)
                erased)
-- Data.Integer.Properties.*-monoʳ-≤-nonPos
d_'42''45'mono'691''45''8804''45'nonPos_6192 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'nonPos_6192 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804''45'nonPos_6192 v0 v2 v3
du_'42''45'mono'691''45''8804''45'nonPos_6192 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'mono'691''45''8804''45'nonPos_6192 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''8804''45'nonPos_6164 (coe v0) (coe v1)
      (coe v2)
-- Data.Integer.Properties.*-monoˡ-<-pos
d_'42''45'mono'737''45''60''45'pos_6214 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'mono'737''45''60''45'pos_6214 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60''45'pos_6214 v0 v2 v3 v4
du_'42''45'mono'737''45''60''45'pos_6214 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'mono'737''45''60''45'pos_6214 v0 v1 v2 v3
  = let v4 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v1 of
         _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
             case coe v3 of
               MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v7
                 -> coe
                      du_'43''9667''45'mono'45''60'_3600
                      (coe addInt (coe v1) (coe mulInt (coe v4) (coe v1)))
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''60''45''8804'_3560
                         (coe v7)
                         (coe
                            MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'691''45''8804'_4080
                            (coe v4) (coe v2)
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854
                               (coe v7))))
               _ -> MAlonzo.RTE.mazUnreachableError
         _ -> case coe v2 of
                _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
                    coe du_'45''9667''60''43''9667'_3642 (coe mulInt (coe v0) (coe v2))
                _ -> case coe v3 of
                       MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v7
                         -> coe
                              MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''60''45''8804'_3560
                                 (coe v7)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'691''45''8804'_4080
                                    (coe v4) (coe subInt (coe (0 :: Integer)) (coe v1))
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854
                                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Integer.Properties.*-monoʳ-<-pos
d_'42''45'mono'691''45''60''45'pos_6246 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'mono'691''45''60''45'pos_6246 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''60''45'pos_6246 v0 v2 v3
du_'42''45'mono'691''45''60''45'pos_6246 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'mono'691''45''60''45'pos_6246 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''60''45'pos_6214 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Properties.*-cancelˡ-<-nonNeg
d_'42''45'cancel'737''45''60''45'nonNeg_6266 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'737''45''60''45'nonNeg_6266 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''60''45'nonNeg_6266 v0 v1 v2 v4
du_'42''45'cancel'737''45''60''45'nonNeg_6266 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'cancel'737''45''60''45'nonNeg_6266 v0 v1 v2 v3
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d_'42''45'cancel'737''45''60'_4208
                     v2 (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                     (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
                     (coe
                        du_'43''9667''45'cancel'45''60'_3612
                        (coe
                           mulInt (coe v2)
                           (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
                        (coe v3)))
            _ -> coe
                   MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                   erased
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
             _ -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                    (coe
                       MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_'42''45'cancel'737''45''60'_4208
                          v2 (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
                          (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                          (coe
                             du_neg'9667''45'cancel'45''60'_3626
                             (coe
                                mulInt (coe v2)
                                (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                             (coe v3))))
-- Data.Integer.Properties.*-cancelʳ-<-nonNeg
d_'42''45'cancel'691''45''60''45'nonNeg_6304 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'691''45''60''45'nonNeg_6304 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''60''45'nonNeg_6304 v0 v1 v2
du_'42''45'cancel'691''45''60''45'nonNeg_6304 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'cancel'691''45''60''45'nonNeg_6304 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonNeg_6266 (coe v0) (coe v1)
      (coe v2)
-- Data.Integer.Properties.*-monoˡ-<-neg
d_'42''45'mono'737''45''60''45'neg_6326 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'mono'737''45''60''45'neg_6326 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60''45'neg_6326 v0 v2 v3 v4
du_'42''45'mono'737''45''60''45'neg_6326 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'mono'737''45''60''45'neg_6326 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v4)
         (coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2))
         (coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
            (\ v5 v6 v7 v8 v9 -> v9)
            (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2))
            (MAlonzo.Code.Data.Integer.Base.d_'45'__252
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                  (coe v2)))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v5 v6 v7 v8 v9 -> v9)
               (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                     (coe v2)))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (\ v5 v6 v7 v8 v9 -> coe du_'60''45'trans_2986 v8 v9)
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                     (\ v5 v6 v7 v8 v9 -> coe du_'60''45''8804''45'trans_2972 v8 v9))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2)))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                     (\ v5 v6 v7 v8 v9 -> v9)
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                     (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                           (coe v1)))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                        (\ v5 v6 v7 v8 v9 -> v9)
                        (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                           (coe
                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                              (coe v1)))
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe d_'8804''45'isPreorder_2800))
                           (coe
                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1)))
                        erased)
                     erased)
                  (coe
                     du_'42''45'mono'737''45''60''45'pos_6214
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v5 v6 -> v6) MAlonzo.Code.Data.Integer.Base.d_'45'__252 v1 v2)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        MAlonzo.Code.Data.Integer.Base.d_'45'__252 (\ v5 v6 -> v5) v1 v2)
                     (coe d_neg'45'mono'45''60'_3302 (coe v1) (coe v2) (coe v3))))
               erased)
            erased))
-- Data.Integer.Properties.*-monoʳ-<-neg
d_'42''45'mono'691''45''60''45'neg_6346 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'mono'691''45''60''45'neg_6346 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''60''45'neg_6346 v0 v2 v3
du_'42''45'mono'691''45''60''45'neg_6346 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'mono'691''45''60''45'neg_6346 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''60''45'neg_6326 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Properties.*-cancelˡ-<-nonPos
d_'42''45'cancel'737''45''60''45'nonPos_6366 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'737''45''60''45'nonPos_6366 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''60''45'nonPos_6366 v0 v1 v2 v4
du_'42''45'cancel'737''45''60''45'nonPos_6366 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'cancel'737''45''60''45'nonPos_6366 v0 v1 v2 v3
  = coe
      d_neg'45'cancel'45''60'_3316 (coe v0) (coe v1)
      (coe
         du_'42''45'cancel'737''45''60''45'nonNeg_6266
         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1))
         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
         (let v4
                = coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
               (coe v4)
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0)))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                  (\ v5 v6 v7 v8 v9 -> v9)
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v0)))
                  (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                        (coe v0)))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v5 v6 v7 v8 v9 -> v9)
                     (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                           (coe v0)))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2) (coe v0))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                           (\ v5 v6 v7 v8 v9 -> coe du_'60''45'trans_2986 v8 v9)
                           (coe
                              MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                           (\ v5 v6 v7 v8 v9 -> coe du_'60''45''8804''45'trans_2972 v8 v9))
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2) (coe v0))
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2) (coe v1))
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                           (\ v5 v6 v7 v8 v9 -> v9)
                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2) (coe v1))
                           (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                              (coe
                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                                 (coe v1)))
                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                              (\ v5 v6 v7 v8 v9 -> v9)
                              (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                                    (coe v1)))
                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                    (coe d_'8804''45'isPreorder_2800))
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v2))
                                    (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1))))
                              erased)
                           erased)
                        v3)
                     erased)
                  erased))))
-- Data.Integer.Properties.*-cancelʳ-<-nonPos
d_'42''45'cancel'691''45''60''45'nonPos_6388 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'691''45''60''45'nonPos_6388 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''60''45'nonPos_6388 v0 v1 v2
du_'42''45'cancel'691''45''60''45'nonPos_6388 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'cancel'691''45''60''45'nonPos_6388 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonPos_6366 (coe v0) (coe v1)
      (coe v2)
-- Data.Integer.Properties.*-cancelˡ-<-neg
d_'42''45'cancel'737''45''60''45'neg_6406 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'737''45''60''45'neg_6406 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonPos_6366 (coe v0) (coe v1)
      (coe subInt (coe (-1 :: Integer)) (coe v2))
-- Data.Integer.Properties.*-cancelʳ-<-neg
d_'42''45'cancel'691''45''60''45'neg_6416 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'691''45''60''45'neg_6416 v0 v1 v2
  = coe
      du_'42''45'cancel'691''45''60''45'nonPos_6388 (coe v0) (coe v1)
      (coe subInt (coe (-1 :: Integer)) (coe v2))
-- Data.Integer.Properties.∣i*j∣≡∣i∣*∣j∣
d_'8739'i'42'j'8739''8801''8739'i'8739''42''8739'j'8739'_6428 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'i'42'j'8739''8801''8739'i'8739''42''8739'j'8739'_6428
  = erased
-- Data.Integer.Properties.i≤j⇒i⊓j≡i
d_i'8804'j'8658'i'8851'j'8801'i_6430 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8804'j'8658'i'8851'j'8801'i_6430 = erased
-- Data.Integer.Properties.i≥j⇒i⊓j≡j
d_i'8805'j'8658'i'8851'j'8801'j_6436 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8805'j'8658'i'8851'j'8801'j_6436 = erased
-- Data.Integer.Properties.i≤j⇒i⊔j≡j
d_i'8804'j'8658'i'8852'j'8801'j_6442 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8804'j'8658'i'8852'j'8801'j_6442 = erased
-- Data.Integer.Properties.i≥j⇒i⊔j≡i
d_i'8805'j'8658'i'8852'j'8801'i_6448 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8805'j'8658'i'8852'j'8801'i_6448 = erased
-- Data.Integer.Properties.⊓-operator
d_'8851''45'operator_6454 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98
d_'8851''45'operator_6454
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MinOperator'46'constructor_1121
      (coe MAlonzo.Code.Data.Integer.Base.d__'8851'__340) erased erased
-- Data.Integer.Properties.⊔-operator
d_'8852''45'operator_6456 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128
d_'8852''45'operator_6456
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MaxOperator'46'constructor_1665
      (coe MAlonzo.Code.Data.Integer.Base.d__'8852'__322) erased erased
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_6468 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'x_6468
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_6470 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8658'x'8851'z'8804'y_6470
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_6472 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8658'z'8851'x'8804'y_6472
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_6474 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8658'x'8851'z'8804'y_6474
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_6476 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8658'z'8851'x'8804'y_6476
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_6478 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8851'z'8658'x'8804'y_6478
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_6480 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8851'z'8658'x'8804'z_6480
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_6482 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'y_6482
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_6484 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8776'x'8658'x'8804'y_6484
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_6486 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8776'y'8658'y'8804'x_6486
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_6488 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'x_6488
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤x⊔y
d_x'8851'y'8804'x'8852'y_6490 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'x'8852'y_6490
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_x'8851'y'8804'x'8852'y_3318
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_6492 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'y_6492
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_6494 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8776'x'8658'x'8804'y_6494
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_6496 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8776'y'8658'y'8804'x_6496
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_6498 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8851'z'8658'x'8804'y_6498
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_6500 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8851'z'8658'x'8804'z_6500
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-absorbs-⊔
d_'8851''45'absorbs'45''8852'_6502 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'absorbs'45''8852'_6502 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_6504 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_6504 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_6506 :: MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8851''45'band_6506
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3052
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_6508 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_6508 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_6510 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'8851''45'commutativeSemigroup_6510
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3054
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-distrib-⊔
d_'8851''45'distrib'45''8852'_6518 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'distrib'45''8852'_6518
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3138
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-properties.⊓-distribʳ-⊔
d_'8851''45'distrib'691''45''8852'_6520 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'691''45''8852'_6520 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-distribˡ-⊔
d_'8851''45'distrib'737''45''8852'_6522 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'737''45''8852'_6522 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_6524 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'glb_6524
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_6526 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_6526 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_6534 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8851''45'isBand_6534
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_6536 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'8851''45'isCommutativeSemigroup_6536
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3036
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_6538 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_6538
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3030
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_6542 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
d_'8851''45'isSelectiveMagma_6542
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_6544 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8851''45'isSemigroup_6544
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_6546 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8851''45'magma_6546
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3048
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_6548 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'45''8804'_6548
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_6552 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'691''45''8804'_6552
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_6554 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'737''45''8804'_6554
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3256
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_6558 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_6558
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_6560 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
d_'8851''45'selectiveMagma_6560
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3056
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_6562 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8851''45'semigroup_6562
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3050
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_6564 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_6564 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-⊔-absorptive
d_'8851''45''8852''45'absorptive_6572 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45''8852''45'absorptive_6572
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'absorptive_3218
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-properties.⊔-absorbs-⊓
d_'8852''45'absorbs'45''8851'_6574 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'absorbs'45''8851'_6574 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_6576 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_6576 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_6578 :: MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8851''45'band_6578
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3052
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_6580 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_6580 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_6582 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'8851''45'commutativeSemigroup_6582
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3054
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊔-distrib-⊓
d_'8852''45'distrib'45''8851'_6590 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'distrib'45''8851'_6590
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'45''8851'_3170
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-properties.⊔-distribʳ-⊓
d_'8852''45'distrib'691''45''8851'_6592 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'691''45''8851'_6592 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊔-distribˡ-⊓
d_'8852''45'distrib'737''45''8851'_6594 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'737''45''8851'_6594 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_6596 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_6596 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_6604 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8851''45'isBand_6604
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_6606 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'8851''45'isCommutativeSemigroup_6606
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3036
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_6608 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_6608
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3030
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_6612 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
d_'8851''45'isSelectiveMagma_6612
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_6614 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8851''45'isSemigroup_6614
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_6616 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'glb_6616
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_6618 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8851''45'magma_6618
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3048
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_6620 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'45''8804'_6620
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_6624 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'691''45''8804'_6624
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_6626 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'737''45''8804'_6626
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3256
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_6628 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_6628
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_6630 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
d_'8851''45'selectiveMagma_6630
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3056
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_6632 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8851''45'semigroup_6632
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3050
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_6634 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_6634 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊔-⊓-absorptive
d_'8852''45''8851''45'absorptive_6642 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45''8851''45'absorptive_6642
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'absorptive_3216
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_6646 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8851''45'isSemilattice_6646
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_602
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_6648 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_6648
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_604
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-⊔-distributiveLattice
d_'8851''45''8852''45'distributiveLattice_6650 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8851''45''8852''45'distributiveLattice_6650
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'distributiveLattice_808
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-⊔-isDistributiveLattice
d_'8851''45''8852''45'isDistributiveLattice_6652 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_'8851''45''8852''45'isDistributiveLattice_6652
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isDistributiveLattice_798
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-⊔-isLattice
d_'8851''45''8852''45'isLattice_6654 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_'8851''45''8852''45'isLattice_6654
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isLattice_796
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-⊔-lattice
d_'8851''45''8852''45'lattice_6656 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8851''45''8852''45'lattice_6656
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'lattice_804
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_6658 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8851''45'isSemilattice_6658
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_602
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_6660 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_6660
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_604
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊔-⊓-distributiveLattice
d_'8852''45''8851''45'distributiveLattice_6662 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8852''45''8851''45'distributiveLattice_6662
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'distributiveLattice_806
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊔-⊓-isDistributiveLattice
d_'8852''45''8851''45'isDistributiveLattice_6664 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_'8852''45''8851''45'isDistributiveLattice_6664
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isDistributiveLattice_800
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊔-⊓-isLattice
d_'8852''45''8851''45'isLattice_6666 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_'8852''45''8851''45'isLattice_6666
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isLattice_794
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊔-⊓-lattice
d_'8852''45''8851''45'lattice_6668 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8852''45''8851''45'lattice_6668
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'lattice_802
      (coe d_'8804''45'totalPreorder_2812)
      (coe d_'8851''45'operator_6454) (coe d_'8852''45'operator_6456)
-- Data.Integer.Properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_6676 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8852'_6676 = erased
-- Data.Integer.Properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_6686 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8851'_6686 = erased
-- Data.Integer.Properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_6696 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8851'_6696 = erased
-- Data.Integer.Properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_6706 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8852'_6706 = erased
-- Data.Integer.Properties.mono-<-distrib-⊓
d_mono'45''60''45'distrib'45''8851'_6716 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''60''45'distrib'45''8851'_6716 = erased
-- Data.Integer.Properties.mono-<-distrib-⊔
d_mono'45''60''45'distrib'45''8852'_6764 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''60''45'distrib'45''8852'_6764 = erased
-- Data.Integer.Properties.antimono-<-distrib-⊔
d_antimono'45''60''45'distrib'45''8852'_6812 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''60''45'distrib'45''8852'_6812 = erased
-- Data.Integer.Properties.antimono-<-distrib-⊓
d_antimono'45''60''45'distrib'45''8851'_6860 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''60''45'distrib'45''8851'_6860 = erased
-- Data.Integer.Properties.neg-distrib-⊔-⊓
d_neg'45'distrib'45''8852''45''8851'_6906 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'45''8852''45''8851'_6906 = erased
-- Data.Integer.Properties.neg-distrib-⊓-⊔
d_neg'45'distrib'45''8851''45''8852'_6912 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'45''8851''45''8852'_6912 = erased
-- Data.Integer.Properties.*-distribˡ-⊓-nonNeg
d_'42''45'distrib'737''45''8851''45'nonNeg_6922 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8851''45'nonNeg_6922 = erased
-- Data.Integer.Properties.*-distribʳ-⊓-nonNeg
d_'42''45'distrib'691''45''8851''45'nonNeg_6938 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8851''45'nonNeg_6938 = erased
-- Data.Integer.Properties.*-distribˡ-⊓-nonPos
d_'42''45'distrib'737''45''8851''45'nonPos_6954 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8851''45'nonPos_6954 = erased
-- Data.Integer.Properties.*-distribʳ-⊓-nonPos
d_'42''45'distrib'691''45''8851''45'nonPos_6970 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8851''45'nonPos_6970 = erased
-- Data.Integer.Properties.*-distribˡ-⊔-nonNeg
d_'42''45'distrib'737''45''8852''45'nonNeg_6986 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8852''45'nonNeg_6986 = erased
-- Data.Integer.Properties.*-distribʳ-⊔-nonNeg
d_'42''45'distrib'691''45''8852''45'nonNeg_7002 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8852''45'nonNeg_7002 = erased
-- Data.Integer.Properties.*-distribˡ-⊔-nonPos
d_'42''45'distrib'737''45''8852''45'nonPos_7018 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8852''45'nonPos_7018 = erased
-- Data.Integer.Properties.*-distribʳ-⊔-nonPos
d_'42''45'distrib'691''45''8852''45'nonPos_7034 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8852''45'nonPos_7034 = erased
-- Data.Integer.Properties.neg-mono-<->
d_neg'45'mono'45''60''45''62'_7042 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_neg'45'mono'45''60''45''62'_7042 = coe d_neg'45'mono'45''60'_3302
-- Data.Integer.Properties.neg-mono-≤-≥
d_neg'45'mono'45''8804''45''8805'_7044 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_neg'45'mono'45''8804''45''8805'_7044 v0 v1 v2
  = coe du_neg'45'mono'45''8804'_3272 v1 v2
-- Data.Integer.Properties.*-monoʳ-≤-non-neg
d_'42''45'mono'691''45''8804''45'non'45'neg_7046 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'non'45'neg_7046 v0 v1 v2 v3 v4
  = coe du_'42''45'mono'691''45''8804''45'nonNeg_6054 v0 v2 v3 v4
-- Data.Integer.Properties.*-monoˡ-≤-non-neg
d_'42''45'mono'737''45''8804''45'non'45'neg_7048 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'non'45'neg_7048 v0 v1 v2 v3
  = coe du_'42''45'mono'737''45''8804''45'nonNeg_6096 v0 v2 v3
-- Data.Integer.Properties.*-cancelˡ-<-non-neg
d_'42''45'cancel'737''45''60''45'non'45'neg_7050 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'737''45''60''45'non'45'neg_7050 v0 v1 v2 v3 v4
  = coe du_'42''45'cancel'737''45''60''45'nonNeg_6266 v0 v1 v2 v4
-- Data.Integer.Properties.*-cancelʳ-<-non-neg
d_'42''45'cancel'691''45''60''45'non'45'neg_7052 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'691''45''60''45'non'45'neg_7052 v0 v1 v2 v3
  = coe du_'42''45'cancel'691''45''60''45'nonNeg_6304 v0 v1 v2
-- Data.Integer.Properties.m≤n⇒m⊓n≡m
d_m'8804'n'8658'm'8851'n'8801'm_7054 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8851'n'8801'm_7054 = erased
-- Data.Integer.Properties.m⊓n≡m⇒m≤n
d_m'8851'n'8801'm'8658'm'8804'n_7056 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8851'n'8801'm'8658'm'8804'n_7056
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
            (coe v0) (coe v1)))
-- Data.Integer.Properties.m≥n⇒m⊓n≡n
d_m'8805'n'8658'm'8851'n'8801'n_7058 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8805'n'8658'm'8851'n'8801'n_7058 = erased
-- Data.Integer.Properties.m⊓n≡n⇒m≥n
d_m'8851'n'8801'n'8658'm'8805'n_7060 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8851'n'8801'n'8658'm'8805'n_7060
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
            (coe v0) (coe v1)))
-- Data.Integer.Properties.m⊓n≤n
d_m'8851'n'8804'n_7062 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8851'n'8804'n_7062
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
            (coe v0) (coe v1)))
-- Data.Integer.Properties.m⊓n≤m
d_m'8851'n'8804'm_7064 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8851'n'8804'm_7064
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8851''45'operator_6454 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
            (coe v0) (coe v1)))
-- Data.Integer.Properties.m≤n⇒m⊔n≡n
d_m'8804'n'8658'm'8852'n'8801'n_7066 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8852'n'8801'n_7066 = erased
-- Data.Integer.Properties.m⊔n≡n⇒m≤n
d_m'8852'n'8801'n'8658'm'8804'n_7068 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8852'n'8801'n'8658'm'8804'n_7068
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.m≥n⇒m⊔n≡m
d_m'8805'n'8658'm'8852'n'8801'm_7070 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8805'n'8658'm'8852'n'8801'm_7070 = erased
-- Data.Integer.Properties.m⊔n≡m⇒m≥n
d_m'8852'n'8801'm'8658'm'8805'n_7072 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8852'n'8801'm'8658'm'8805'n_7072
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.m≤m⊔n
d_m'8804'm'8852'n_7074 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'm'8852'n_7074
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.n≤m⊔n
d_n'8804'm'8852'n_7076 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_n'8804'm'8852'n_7076
  = let v0 = d_'8804''45'totalPreorder_2812 in
    coe
      (let v1 = d_'8852''45'operator_6456 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Integer.Properties.+-pos-monoʳ-≤
d_'43''45'pos'45'mono'691''45''8804'_7080 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'pos'45'mono'691''45''8804'_7080 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
        -> coe
             d_'8854''45'mono'691''45''8805''45''8804'_4024 (coe v0)
             (coe subInt (coe (0 :: Integer)) (coe v1))
             (coe subInt (coe (0 :: Integer)) (coe v2))
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe
             du_'8804''45'trans_2730
             (coe
                d_m'8854'n'8804'm_3912 (coe v0)
                (coe subInt (coe (0 :: Integer)) (coe v1)))
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3482 (coe v0)))
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''8804'_3554
                (coe v0) (coe v2) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.+-neg-monoʳ-≤
d_'43''45'neg'45'mono'691''45''8804'_7096 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'neg'45'mono'691''45''8804'_7096 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
        -> let v7 = subInt (coe (-1 :: Integer)) (coe v1) in
           coe
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''8804'_3554
                   (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v7) (coe v6)))
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe
             du_'8804''45'trans_2730
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3482
                   (coe addInt (coe (1 :: Integer)) (coe v0))))
             (coe
                d_'45'1'43'm'8804'n'8854'm_3992
                (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
        -> coe
             d_'8854''45'mono'737''45''8804'_4056
             (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1) (coe v2)
             (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.n≮n
d_n'8814'n_7110 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8814'n_7110 = erased
-- Data.Integer.Properties.∣n∣≡0⇒n≡0
d_'8739'n'8739''8801'0'8658'n'8801'0_7112 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'n'8739''8801'0'8658'n'8801'0_7112 = erased
-- Data.Integer.Properties.∣-n∣≡∣n∣
d_'8739''45'n'8739''8801''8739'n'8739'_7114 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45'n'8739''8801''8739'n'8739'_7114 = erased
-- Data.Integer.Properties.0≤n⇒+∣n∣≡n
d_0'8804'n'8658''43''8739'n'8739''8801'n_7116 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8804'n'8658''43''8739'n'8739''8801'n_7116 = erased
-- Data.Integer.Properties.+∣n∣≡n⇒0≤n
d_'43''8739'n'8739''8801'n'8658'0'8804'n_7118 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''8739'n'8739''8801'n'8658'0'8804'n_7118 v0 v1
  = coe du_'43''8739'i'8739''8801'i'8658'0'8804'i_3352
-- Data.Integer.Properties.+∣n∣≡n⊎+∣n∣≡-n
d_'43''8739'n'8739''8801'n'8846''43''8739'n'8739''8801''45'n_7120 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'43''8739'n'8739''8801'n'8846''43''8739'n'8739''8801''45'n_7120
  = coe
      d_'43''8739'i'8739''8801'i'8846''43''8739'i'8739''8801''45'i_3358
-- Data.Integer.Properties.∣m+n∣≤∣m∣+∣n∣
d_'8739'm'43'n'8739''8804''8739'm'8739''43''8739'n'8739'_7122 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'43'n'8739''8804''8739'm'8739''43''8739'n'8739'_7122
  = coe d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3398
-- Data.Integer.Properties.∣m-n∣≤∣m∣+∣n∣
d_'8739'm'45'n'8739''8804''8739'm'8739''43''8739'n'8739'_7124 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'45'n'8739''8804''8739'm'8739''43''8739'n'8739'_7124
  = coe d_'8739'i'45'j'8739''8804''8739'i'8739''43''8739'j'8739'_3436
-- Data.Integer.Properties.signₙ◃∣n∣≡n
d_sign'8345''9667''8739'n'8739''8801'n_7126 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'8345''9667''8739'n'8739''8801'n_7126 = erased
-- Data.Integer.Properties.◃-≡
d_'9667''45''8801'_7128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45''8801'_7128 = erased
-- Data.Integer.Properties.∣m-n∣≡∣n-m∣
d_'8739'm'45'n'8739''8801''8739'n'45'm'8739'_7130 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'45'n'8739''8801''8739'n'45'm'8739'_7130 = erased
-- Data.Integer.Properties.m≡n⇒m-n≡0
d_m'8801'n'8658'm'45'n'8801'0_7132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8801'n'8658'm'45'n'8801'0_7132 = erased
-- Data.Integer.Properties.m-n≡0⇒m≡n
d_m'45'n'8801'0'8658'm'8801'n_7134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'45'n'8801'0'8658'm'8801'n_7134 = erased
-- Data.Integer.Properties.≤-steps
d_'8804''45'steps_7136 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'steps_7136 v0 v1 v2 v3 v4
  = coe du_i'8804'j'8658'i'8804'k'43'j_4578 v0 v1 v2 v4
-- Data.Integer.Properties.≤-steps-neg
d_'8804''45'steps'45'neg_7138 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'steps'45'neg_7138 v0 v1 v2 v3 v4
  = coe du_i'8804'j'8658'i'45'k'8804'j_4852 v0 v2 v4
-- Data.Integer.Properties.≤-step
d_'8804''45'step_7140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'step_7140 = coe d_i'8804'j'8658'i'8804'1'43'j_4948
-- Data.Integer.Properties.≤-step-neg
d_'8804''45'step'45'neg_7142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'step'45'neg_7142 v0 v1 v2
  = coe du_i'8804'j'8658'pred'91'i'93''8804'j_5116 v2
-- Data.Integer.Properties.m≤n⇒m-n≤0
d_m'8804'n'8658'm'45'n'8804'0_7144 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'n'8658'm'45'n'8804'0_7144
  = coe d_i'8804'j'8658'i'45'j'8804'0_4886
-- Data.Integer.Properties.m-n≤0⇒m≤n
d_m'45'n'8804'0'8658'm'8804'n_7146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'45'n'8804'0'8658'm'8804'n_7146
  = coe d_i'45'j'8804'0'8658'i'8804'j_4912
-- Data.Integer.Properties.m≤n⇒0≤n-m
d_m'8804'n'8658'0'8804'n'45'm_7148 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'n'8658'0'8804'n'45'm_7148
  = coe d_i'8804'j'8658'0'8804'j'45'i_4924
-- Data.Integer.Properties.0≤n-m⇒m≤n
d_0'8804'n'45'm'8658'm'8804'n_7150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_0'8804'n'45'm'8658'm'8804'n_7150
  = coe d_0'8804'i'45'j'8658'j'8804'i_4936
-- Data.Integer.Properties.n≤1+n
d_n'8804'1'43'n_7152 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_n'8804'1'43'n_7152 = coe d_i'8804'suc'91'i'93'_4952
-- Data.Integer.Properties.n≢1+n
d_n'8802'1'43'n_7154 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'1'43'n_7154 = erased
-- Data.Integer.Properties.m≤pred[n]⇒m<n
d_m'8804'pred'91'n'93''8658'm'60'n_7156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_m'8804'pred'91'n'93''8658'm'60'n_7156 v0 v1 v2
  = coe du_i'8804'pred'91'j'93''8658'i'60'j_5094 v1 v2
-- Data.Integer.Properties.m<n⇒m≤pred[n]
d_m'60'n'8658'm'8804'pred'91'n'93'_7158 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'60'n'8658'm'8804'pred'91'n'93'_7158 v0 v1 v2
  = coe du_i'60'j'8658'i'8804'pred'91'j'93'_5104 v1 v2
-- Data.Integer.Properties.-1*n≡-n
d_'45'1'42'n'8801''45'n_7160 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45'1'42'n'8801''45'n_7160 = erased
-- Data.Integer.Properties.m*n≡0⇒m≡0∨n≡0
d_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_7162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_7162 v0 v1 v2
  = coe du_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5780 v0
-- Data.Integer.Properties.∣m*n∣≡∣m∣*∣n∣
d_'8739'm'42'n'8739''8801''8739'm'8739''42''8739'n'8739'_7164 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'42'n'8739''8801''8739'm'8739''42''8739'n'8739'_7164
  = erased
-- Data.Integer.Properties.n≤m+n
d_n'8804'm'43'n_7168 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_n'8804'm'43'n_7168 v0 v1
  = coe du_i'8804'j'43'i_4592 (coe v0) (coe v1)
-- Data.Integer.Properties.m≤m+n
d_m'8804'm'43'n_7176 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'm'43'n_7176 v0 v1
  = coe du_i'8804'i'43'j_4604 (coe v0) (coe v1)
-- Data.Integer.Properties.m-n≤m
d_m'45'n'8804'm_7186 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'45'n'8804'm_7186 v0 v1
  = coe du_i'45'j'8804'i_4880 (coe v0) (coe v1)
-- Data.Integer.Properties.*-monoʳ-≤-pos
d_'42''45'mono'691''45''8804''45'pos_7196 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'pos_7196 v0 v1 v2
  = coe
      du_'42''45'mono'691''45''8804''45'nonNeg_6054
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1) (coe v2)
-- Data.Integer.Properties.*-monoˡ-≤-pos
d_'42''45'mono'737''45''8804''45'pos_7204 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'pos_7204 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''8804''45'nonNeg_6096
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1) (coe v2)
-- Data.Integer.Properties.*-monoˡ-≤-neg
d_'42''45'mono'737''45''8804''45'neg_7212 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'neg_7212 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''8804''45'nonPos_6164
      (coe subInt (coe (-1 :: Integer)) (coe v0)) (coe v1) (coe v2)
-- Data.Integer.Properties.*-monoʳ-≤-neg
d_'42''45'mono'691''45''8804''45'neg_7220 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'neg_7220 v0 v1 v2
  = coe
      du_'42''45'mono'691''45''8804''45'nonPos_6192
      (coe subInt (coe (-1 :: Integer)) (coe v0)) (coe v1) (coe v2)
-- Data.Integer.Properties.pos-+-commute
d_pos'45''43''45'commute_7224 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pos'45''43''45'commute_7224 = erased
-- Data.Integer.Properties.abs-*-commute
d_abs'45''42''45'commute_7226 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45''42''45'commute_7226 = erased
-- Data.Integer.Properties.pos-distrib-*
d_pos'45'distrib'45''42'_7232 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pos'45'distrib'45''42'_7232 = erased
-- Data.Integer.Properties.+-isAbelianGroup
d_'43''45'isAbelianGroup_7238 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_7238
  = coe d_'43''45'0'45'isAbelianGroup_4436
