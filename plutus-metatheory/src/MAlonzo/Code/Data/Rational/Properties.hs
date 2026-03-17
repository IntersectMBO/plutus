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

module MAlonzo.Code.Data.Rational.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Apartness.Bundles
import qualified MAlonzo.Code.Algebra.Apartness.Structures
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Morphism.GroupMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.RingMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Coprimality
import qualified MAlonzo.Code.Data.Integer.GCD
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.GCD
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Unnormalised.Base
import qualified MAlonzo.Code.Data.Rational.Unnormalised.Properties
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Morphism.RelMonomorphism
import qualified MAlonzo.Code.Relation.Binary.Morphism.Structures
import qualified MAlonzo.Code.Relation.Binary.Properties.DecSetoid
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core

-- Data.Rational.Properties._._DistributesOver_
d__DistributesOver__10 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d__DistributesOver__10 = erased
-- Data.Rational.Properties._._DistributesOverʳ_
d__DistributesOver'691'__12 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d__DistributesOver'691'__12 = erased
-- Data.Rational.Properties._._DistributesOverˡ_
d__DistributesOver'737'__14 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d__DistributesOver'737'__14 = erased
-- Data.Rational.Properties._.Associative
d_Associative_30 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_Associative_30 = erased
-- Data.Rational.Properties._.Commutative
d_Commutative_34 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_Commutative_34 = erased
-- Data.Rational.Properties._.Congruent₁
d_Congruent'8321'_36 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_Congruent'8321'_36 = erased
-- Data.Rational.Properties._.Identity
d_Identity_50 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_Identity_50 = erased
-- Data.Rational.Properties._.Inverse
d_Inverse_54 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_Inverse_54 = erased
-- Data.Rational.Properties._.Invertible
d_Invertible_56 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 -> ()
d_Invertible_56 = erased
-- Data.Rational.Properties._.LeftIdentity
d_LeftIdentity_76 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_LeftIdentity_76 = erased
-- Data.Rational.Properties._.LeftInverse
d_LeftInverse_78 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_LeftInverse_78 = erased
-- Data.Rational.Properties._.LeftZero
d_LeftZero_84 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_LeftZero_84 = erased
-- Data.Rational.Properties._.RightIdentity
d_RightIdentity_106 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_RightIdentity_106 = erased
-- Data.Rational.Properties._.RightInverse
d_RightInverse_108 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_RightInverse_108 = erased
-- Data.Rational.Properties._.RightZero
d_RightZero_114 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_RightZero_114 = erased
-- Data.Rational.Properties._.Zero
d_Zero_134 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  ()
d_Zero_134 = erased
-- Data.Rational.Properties._.IsAbelianGroup
d_IsAbelianGroup_138 a0 a1 a2 = ()
-- Data.Rational.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_150 a0 a1 = ()
-- Data.Rational.Properties._.IsCommutativeRing
d_IsCommutativeRing_152 a0 a1 a2 a3 a4 = ()
-- Data.Rational.Properties._.IsGroup
d_IsGroup_162 a0 a1 a2 = ()
-- Data.Rational.Properties._.IsMagma
d_IsMagma_182 a0 = ()
-- Data.Rational.Properties._.IsMonoid
d_IsMonoid_188 a0 a1 = ()
-- Data.Rational.Properties._.IsRing
d_IsRing_204 a0 a1 a2 a3 a4 = ()
-- Data.Rational.Properties._.IsSemigroup
d_IsSemigroup_210 a0 = ()
-- Data.Rational.Properties._.IsAbelianGroup.comm
d_comm_230 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_230 = erased
-- Data.Rational.Properties._.IsAbelianGroup.isGroup
d_isGroup_252 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_isGroup_252 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v0)
-- Data.Rational.Properties._.IsCommutativeMonoid.comm
d_comm_520 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_520 = erased
-- Data.Rational.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_536 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_536 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v0)
-- Data.Rational.Properties._.IsCommutativeRing.*-comm
d_'42''45'comm_566 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_566 = erased
-- Data.Rational.Properties._.IsCommutativeRing.isRing
d_isRing_654 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_isRing_654 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0)
-- Data.Rational.Properties._.IsGroup.inverse
d_inverse_928 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_928 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1050 (coe v0)
-- Data.Rational.Properties._.IsGroup.isMonoid
d_isMonoid_942 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_942 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v0)
-- Data.Rational.Properties._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_964 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_964 = erased
-- Data.Rational.Properties._.IsMagma.isEquivalence
d_isEquivalence_1492 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1492 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v0)
-- Data.Rational.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1506 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1506 = erased
-- Data.Rational.Properties._.IsMonoid.identity
d_identity_1602 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1602 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_696 (coe v0)
-- Data.Rational.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1614 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_1614 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v0)
-- Data.Rational.Properties._.IsRing.*-assoc
d_'42''45'assoc_2120 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2120 = erased
-- Data.Rational.Properties._.IsRing.*-cong
d_'42''45'cong_2122 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2122 = erased
-- Data.Rational.Properties._.IsRing.*-identity
d_'42''45'identity_2128 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2128 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2698 (coe v0)
-- Data.Rational.Properties._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2156 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
d_'43''45'isAbelianGroup_2156 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
      (coe v0)
-- Data.Rational.Properties._.IsRing.distrib
d_distrib_2186 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2186 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2700 (coe v0)
-- Data.Rational.Properties._.IsSemigroup.assoc
d_assoc_2348 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2348 = erased
-- Data.Rational.Properties._.IsSemigroup.isMagma
d_isMagma_2352 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2352 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v0)
-- Data.Rational.Properties.mkℚ-cong
d_mkℚ'45'cong_2690 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkℚ'45'cong_2690 = erased
-- Data.Rational.Properties.mkℚ-injective
d_mkℚ'45'injective_2704 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mkℚ'45'injective_2704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_mkℚ'45'injective_2704
du_mkℚ'45'injective_2704 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mkℚ'45'injective_2704
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Rational.Properties._≟_
d__'8799'__2706 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__2706 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe MAlonzo.Code.Data.Product.Base.du_uncurry_244 erased)
                    (\ v8 -> coe du_mkℚ'45'injective_2704)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe
                          MAlonzo.Code.Data.Integer.Properties.d__'8799'__2714 (coe v2)
                          (coe v5))
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710 (coe v3)
                          (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.≡-setoid
d_'8801''45'setoid_2716 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8801''45'setoid_2716
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Rational.Properties.≡-decSetoid
d_'8801''45'decSetoid_2718 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86
d_'8801''45'decSetoid_2718
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__2706)
-- Data.Rational.Properties.1≢0
d_1'8802'0_2720 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'8802'0_2720 = erased
-- Data.Rational.Properties.mkℚ+-cong
d_mkℚ'43''45'cong_2738 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkℚ'43''45'cong_2738 = erased
-- Data.Rational.Properties.mkℚ+-injective
d_mkℚ'43''45'injective_2756 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mkℚ'43''45'injective_2756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_mkℚ'43''45'injective_2756
du_mkℚ'43''45'injective_2756 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mkℚ'43''45'injective_2756
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Rational.Properties.↥-mkℚ+
d_'8613''45'mkℚ'43'_2766 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''45'mkℚ'43'_2766 = erased
-- Data.Rational.Properties.↧-mkℚ+
d_'8615''45'mkℚ'43'_2780 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''45'mkℚ'43'_2780 = erased
-- Data.Rational.Properties.mkℚ+-nonNeg
d_mkℚ'43''45'nonNeg_2794 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_mkℚ'43''45'nonNeg_2794 ~v0 ~v1 ~v2 ~v3
  = du_mkℚ'43''45'nonNeg_2794
du_mkℚ'43''45'nonNeg_2794 ::
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_mkℚ'43''45'nonNeg_2794
  = coe
      MAlonzo.Code.Data.Integer.Base.C_NonNegative'46'constructor_1457
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Rational.Properties.mkℚ+-pos
d_mkℚ'43''45'pos_2810 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_mkℚ'43''45'pos_2810 ~v0 ~v1 ~v2 ~v3 ~v4 = du_mkℚ'43''45'pos_2810
du_mkℚ'43''45'pos_2810 ::
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_mkℚ'43''45'pos_2810
  = coe
      MAlonzo.Code.Data.Integer.Base.C_Positive'46'constructor_1399
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Rational.Properties.drop-*≡*
d_drop'45''42''8801''42'_2816 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''42''8801''42'_2816 = erased
-- Data.Rational.Properties.≡⇒≃
d_'8801''8658''8771'_2820 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40
d_'8801''8658''8771'_2820 ~v0 ~v1 ~v2 = du_'8801''8658''8771'_2820
du_'8801''8658''8771'_2820 ::
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40
du_'8801''8658''8771'_2820
  = coe MAlonzo.Code.Data.Rational.Base.C_'42''8801''42'_46
-- Data.Rational.Properties.≃⇒≡
d_'8771''8658''8801'_2822 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8771''8658''8801'_2822 = erased
-- Data.Rational.Properties._.1+d₂∣1+d₁
d_1'43'd'8322''8739'1'43'd'8321'_2844 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_1'43'd'8322''8739'1'43'd'8321'_2844 v0 v1 ~v2 v3 v4 ~v5 ~v6
  = du_1'43'd'8322''8739'1'43'd'8321'_2844 v0 v1 v3 v4
du_1'43'd'8322''8739'1'43'd'8321'_2844 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_1'43'd'8322''8739'1'43'd'8321'_2844 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Integer.Coprimality.du_coprime'45'divisor_22
      (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v2)
      (coe addInt (coe (1 :: Integer)) (coe v1))
      (coe
         MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
-- Data.Rational.Properties._.helper
d_helper_2846 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_2846 = erased
-- Data.Rational.Properties.≃-sym
d_'8771''45'sym_2856 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40
d_'8771''45'sym_2856 ~v0 ~v1 = du_'8771''45'sym_2856
du_'8771''45'sym_2856 ::
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40
du_'8771''45'sym_2856
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (\ v0 -> coe du_'8801''8658''8771'_2820)
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216 erased erased)
-- Data.Rational.Properties.↥p≡0⇒p≡0
d_'8613'p'8801'0'8658'p'8801'0_2860 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613'p'8801'0'8658'p'8801'0_2860 = erased
-- Data.Rational.Properties._.d-1≡0
d_d'45'1'8801'0_2872 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_d'45'1'8801'0_2872 = erased
-- Data.Rational.Properties.p≡0⇒↥p≡0
d_p'8801'0'8658''8613'p'8801'0_2876 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'8801'0'8658''8613'p'8801'0_2876 = erased
-- Data.Rational.Properties.↥p≡↥q≡0⇒p≡q
d_'8613'p'8801''8613'q'8801'0'8658'p'8801'q_2884 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613'p'8801''8613'q'8801'0'8658'p'8801'q_2884 = erased
-- Data.Rational.Properties.nonNeg≢neg
d_nonNeg'8802'neg_2898 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nonNeg'8802'neg_2898 = erased
-- Data.Rational.Properties.pos⇒nonNeg
d_pos'8658'nonNeg_2902 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_pos'8658'nonNeg_2902 v0 ~v1 = du_pos'8658'nonNeg_2902 v0
du_pos'8658'nonNeg_2902 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_pos'8658'nonNeg_2902 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_pos'8658'nonNeg_950
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
-- Data.Rational.Properties.neg⇒nonPos
d_neg'8658'nonPos_2908 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
d_neg'8658'nonPos_2908 v0 ~v1 = du_neg'8658'nonPos_2908 v0
du_neg'8658'nonPos_2908 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
du_neg'8658'nonPos_2908 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_neg'8658'nonPos_956
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
-- Data.Rational.Properties.nonNeg∧nonZero⇒pos
d_nonNeg'8743'nonZero'8658'pos_2914 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_nonNeg'8743'nonZero'8658'pos_2914 v0 ~v1 ~v2
  = du_nonNeg'8743'nonZero'8658'pos_2914 v0
du_nonNeg'8743'nonZero'8658'pos_2914 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_nonNeg'8743'nonZero'8658'pos_2914 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_Positive'46'constructor_1399
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Properties.pos⇒nonZero
d_pos'8658'nonZero_2918 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_pos'8658'nonZero_2918 v0 ~v1 = du_pos'8658'nonZero_2918 v0
du_pos'8658'nonZero_2918 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_pos'8658'nonZero_2918 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Properties.neg⇒nonZero
d_neg'8658'nonZero_2922 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_neg'8658'nonZero_2922 v0 ~v1 = du_neg'8658'nonZero_2922 v0
du_neg'8658'nonZero_2922 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_neg'8658'nonZero_2922 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Properties.↥-neg
d_'8613''45'neg_2926 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''45'neg_2926 = erased
-- Data.Rational.Properties.↧-neg
d_'8615''45'neg_2930 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''45'neg_2930 = erased
-- Data.Rational.Properties.neg-injective
d_neg'45'injective_2932 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'injective_2932 = erased
-- Data.Rational.Properties.neg-pos
d_neg'45'pos_2954 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_neg'45'pos_2954 v0 ~v1 = du_neg'45'pos_2954 v0
du_neg'45'pos_2954 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_neg'45'pos_2954 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_Negative'46'constructor_1573
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Properties.normalize-coprime
d_normalize'45'coprime_2962 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalize'45'coprime_2962 = erased
-- Data.Rational.Properties._.d
d_d_2974 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer
d_d_2974 ~v0 v1 ~v2 = du_d_2974 v1
du_d_2974 :: Integer -> Integer
du_d_2974 v0 = coe addInt (coe (1 :: Integer)) (coe v0)
-- Data.Rational.Properties._.g
d_g_2976 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer
d_g_2976 v0 v1 ~v2 = du_g_2976 v0 v1
du_g_2976 :: Integer -> Integer -> Integer
du_g_2976 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0)
      (coe du_d_2974 (coe v1))
-- Data.Rational.Properties._.c′
d_c'8242'_2978 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8242'_2978 = erased
-- Data.Rational.Properties._.c₂
d_c'8322'_2980 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'8322'_2980 = erased
-- Data.Rational.Properties._.g≡1
d_g'8801'1_2982 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_g'8801'1_2982 = erased
-- Data.Rational.Properties._.g≢0
d_g'8802'0_2984 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_g'8802'0_2984 v0 v1 ~v2 = du_g'8802'0_2984 v0 v1
du_g'8802'0_2984 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_g'8802'0_2984 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'8802''45'nonZero_126
      (coe
         MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0)
         (coe du_d_2974 (coe v1)))
-- Data.Rational.Properties.↥-normalize
d_'8613''45'normalize_2998 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''45'normalize_2998 = erased
-- Data.Rational.Properties._.g
d_g_3008 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_g_3008 v0 v1 ~v2 = du_g_3008 v0 v1
du_g_3008 :: Integer -> Integer -> Integer
du_g_3008 v0 v1
  = coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1)
-- Data.Rational.Properties._.g≢0
d_g'8802'0_3010 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_g'8802'0_3010 v0 v1 ~v2 = du_g'8802'0_3010 v0 v1
du_g'8802'0_3010 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_g'8802'0_3010 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'8802''45'nonZero_126
      (coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1))
-- Data.Rational.Properties._.i/g
d_i'47'g_3014 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_i'47'g_3014 v0 v1 ~v2 = du_i'47'g_3014 v0 v1
du_i'47'g_3014 :: Integer -> Integer -> Integer
du_i'47'g_3014 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'47'__314 (coe v0)
      (coe du_g_3008 (coe v0) (coe v1))
-- Data.Rational.Properties.↧-normalize
d_'8615''45'normalize_3026 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''45'normalize_3026 = erased
-- Data.Rational.Properties._.g
d_g_3036 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_g_3036 v0 v1 ~v2 = du_g_3036 v0 v1
du_g_3036 :: Integer -> Integer -> Integer
du_g_3036 v0 v1
  = coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1)
-- Data.Rational.Properties.normalize-cong
d_normalize'45'cong_3058 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalize'45'cong_3058 = erased
-- Data.Rational.Properties._.g
d_g_3068 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_g_3068 v0 v1 ~v2 ~v3 = du_g_3068 v0 v1
du_g_3068 :: Integer -> Integer -> Integer
du_g_3068 v0 v1
  = coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1)
-- Data.Rational.Properties.normalize-nonNeg
d_normalize'45'nonNeg_3080 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_normalize'45'nonNeg_3080 ~v0 ~v1 ~v2
  = du_normalize'45'nonNeg_3080
du_normalize'45'nonNeg_3080 ::
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_normalize'45'nonNeg_3080 = coe du_mkℚ'43''45'nonNeg_2794
-- Data.Rational.Properties._.g
d_g_3090 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_g_3090 v0 v1 ~v2 = du_g_3090 v0 v1
du_g_3090 :: Integer -> Integer -> Integer
du_g_3090 v0 v1
  = coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1)
-- Data.Rational.Properties.normalize-pos
d_normalize'45'pos_3104 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_normalize'45'pos_3104 ~v0 ~v1 ~v2 ~v3 = du_normalize'45'pos_3104
du_normalize'45'pos_3104 ::
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_normalize'45'pos_3104 = coe du_mkℚ'43''45'pos_2810
-- Data.Rational.Properties._.g≢0
d_g'8802'0_3116 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_g'8802'0_3116 v0 v1 ~v2 ~v3 = du_g'8802'0_3116 v0 v1
du_g'8802'0_3116 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_g'8802'0_3116 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'8802''45'nonZero_126
      (coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1))
-- Data.Rational.Properties.normalize-injective-≃
d_normalize'45'injective'45''8771'_3134 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_normalize'45'injective'45''8771'_3134 = erased
-- Data.Rational.Properties._.gcd[m,c]
d_gcd'91'm'44'c'93'_3150 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_gcd'91'm'44'c'93'_3150 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_gcd'91'm'44'c'93'_3150 v0 v2
du_gcd'91'm'44'c'93'_3150 :: Integer -> Integer -> Integer
du_gcd'91'm'44'c'93'_3150 v0 v1
  = coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1)
-- Data.Rational.Properties._.gcd[n,d]
d_gcd'91'n'44'd'93'_3152 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_gcd'91'n'44'd'93'_3152 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_gcd'91'n'44'd'93'_3152 v1 v3
du_gcd'91'n'44'd'93'_3152 :: Integer -> Integer -> Integer
du_gcd'91'n'44'd'93'_3152 v0 v1
  = coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1)
-- Data.Rational.Properties._.gcd[m,c]∣m
d_gcd'91'm'44'c'93''8739'm_3154 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'm'44'c'93''8739'm_3154 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_gcd'91'm'44'c'93''8739'm_3154 v0 v2
du_gcd'91'm'44'c'93''8739'm_3154 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_gcd'91'm'44'c'93''8739'm_3154 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd'91'm'44'n'93''8739'm_248 (coe v0)
      (coe v1)
-- Data.Rational.Properties._.gcd[m,c]∣c
d_gcd'91'm'44'c'93''8739'c_3156 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'm'44'c'93''8739'c_3156 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_gcd'91'm'44'c'93''8739'c_3156 v0 v2
du_gcd'91'm'44'c'93''8739'c_3156 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_gcd'91'm'44'c'93''8739'c_3156 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd'91'm'44'n'93''8739'n_278 (coe v0)
      (coe v1)
-- Data.Rational.Properties._.gcd[n,d]∣n
d_gcd'91'n'44'd'93''8739'n_3158 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'n'44'd'93''8739'n_3158 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_gcd'91'n'44'd'93''8739'n_3158 v1 v3
du_gcd'91'n'44'd'93''8739'n_3158 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_gcd'91'n'44'd'93''8739'n_3158 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd'91'm'44'n'93''8739'm_248 (coe v0)
      (coe v1)
-- Data.Rational.Properties._.gcd[n,d]∣d
d_gcd'91'n'44'd'93''8739'd_3160 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'n'44'd'93''8739'd_3160 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_gcd'91'n'44'd'93''8739'd_3160 v1 v3
du_gcd'91'n'44'd'93''8739'd_3160 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_gcd'91'n'44'd'93''8739'd_3160 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd'91'm'44'n'93''8739'n_278 (coe v0)
      (coe v1)
-- Data.Rational.Properties._.md∣gcd[m,c]gcd[n,d]
d_md'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3162 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_md'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3162 v0 v1 v2 v3 ~v4
                                                  ~v5 ~v6
  = du_md'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3162 v0 v1 v2 v3
du_md'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3162 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_md'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3162 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'pres'45''8739'_410
      (coe du_gcd'91'm'44'c'93''8739'm_3154 (coe v0) (coe v2))
      (coe du_gcd'91'n'44'd'93''8739'd_3160 (coe v1) (coe v3))
-- Data.Rational.Properties._.nc∣gcd[n,d]gcd[m,c]
d_nc'8739'gcd'91'n'44'd'93'gcd'91'm'44'c'93'_3164 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_nc'8739'gcd'91'n'44'd'93'gcd'91'm'44'c'93'_3164 v0 v1 v2 v3 ~v4
                                                  ~v5 ~v6
  = du_nc'8739'gcd'91'n'44'd'93'gcd'91'm'44'c'93'_3164 v0 v1 v2 v3
du_nc'8739'gcd'91'n'44'd'93'gcd'91'm'44'c'93'_3164 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_nc'8739'gcd'91'n'44'd'93'gcd'91'm'44'c'93'_3164 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'pres'45''8739'_410
      (coe du_gcd'91'n'44'd'93''8739'n_3158 (coe v1) (coe v3))
      (coe du_gcd'91'm'44'c'93''8739'c_3156 (coe v0) (coe v2))
-- Data.Rational.Properties._.nc∣gcd[m,c]gcd[n,d]
d_nc'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3166 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_nc'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3166 v0 v1 v2 v3 ~v4
                                                  ~v5 ~v6
  = du_nc'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3166 v0 v1 v2 v3
du_nc'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3166 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_nc'8739'gcd'91'm'44'c'93'gcd'91'n'44'd'93'_3166 v0 v1 v2 v3
  = coe
      du_nc'8739'gcd'91'n'44'd'93'gcd'91'm'44'c'93'_3164 (coe v0)
      (coe v1) (coe v2) (coe v3)
-- Data.Rational.Properties._.gcd[m,c]≢0′
d_gcd'91'm'44'c'93''8802'0'8242'_3170 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_gcd'91'm'44'c'93''8802'0'8242'_3170 = erased
-- Data.Rational.Properties._.gcd[n,d]≢0′
d_gcd'91'n'44'd'93''8802'0'8242'_3172 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_gcd'91'n'44'd'93''8802'0'8242'_3172 = erased
-- Data.Rational.Properties._.gcd[m,c]≢0
d_gcd'91'm'44'c'93''8802'0_3174 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_gcd'91'm'44'c'93''8802'0_3174 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
  = du_gcd'91'm'44'c'93''8802'0_3174 v0 v2
du_gcd'91'm'44'c'93''8802'0_3174 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_gcd'91'm'44'c'93''8802'0_3174 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'8802''45'nonZero_126
      (coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1))
-- Data.Rational.Properties._.gcd[n,d]≢0
d_gcd'91'n'44'd'93''8802'0_3176 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_gcd'91'n'44'd'93''8802'0_3176 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_gcd'91'n'44'd'93''8802'0_3176 v1 v3
du_gcd'91'n'44'd'93''8802'0_3176 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_gcd'91'n'44'd'93''8802'0_3176 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'8802''45'nonZero_126
      (coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1))
-- Data.Rational.Properties._.div
d_div_3186 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_div_3186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_div_3186
du_div_3186 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_div_3186 = coe du_mkℚ'43''45'injective_2756
-- Data.Rational.Properties._.m/gcd[m,c]≡n/gcd[n,d]
d_m'47'gcd'91'm'44'c'93''8801'n'47'gcd'91'n'44'd'93'_3188 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'47'gcd'91'm'44'c'93''8801'n'47'gcd'91'n'44'd'93'_3188 = erased
-- Data.Rational.Properties._.c/gcd[m,c]≡d/gcd[n,d]
d_c'47'gcd'91'm'44'c'93''8801'd'47'gcd'91'n'44'd'93'_3190 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'47'gcd'91'm'44'c'93''8801'd'47'gcd'91'n'44'd'93'_3190 = erased
-- Data.Rational.Properties.↥-/
d_'8613''45''47'_3198 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''45''47'_3198 = erased
-- Data.Rational.Properties._.g
d_g_3212 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_g_3212 v0 v1 ~v2 = du_g_3212 v0 v1
du_g_3212 :: Integer -> Integer -> Integer
du_g_3212 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd_152
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Rational.Properties._.norm
d_norm_3214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_norm_3214 v0 v1 ~v2 = du_norm_3214 v0 v1
du_norm_3214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_norm_3214 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Base.du_normalize_136
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Rational.Properties.↧-/
d_'8615''45''47'_3224 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''45''47'_3224 = erased
-- Data.Rational.Properties._.g
d_g_3238 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_g_3238 v0 v1 ~v2 = du_g_3238 v0 v1
du_g_3238 :: Integer -> Integer -> Integer
du_g_3238 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd_152
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Rational.Properties._.norm
d_norm_3240 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_norm_3240 v0 v1 ~v2 = du_norm_3240 v0 v1
du_norm_3240 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
du_norm_3240 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Base.du_normalize_136
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Rational.Properties.↥p/↧p≡p
d_'8613'p'47''8615'p'8801'p_3246 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613'p'47''8615'p'8801'p_3246 = erased
-- Data.Rational.Properties.0/n≡0
d_0'47'n'8801'0_3264 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'47'n'8801'0_3264 = erased
-- Data.Rational.Properties._.0-cop-1
d_0'45'cop'45'1_3276 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'45'cop'45'1_3276 = erased
-- Data.Rational.Properties._.n/n≢0
d_n'47'n'8802'0_3278 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_n'47'n'8802'0_3278 ~v0 ~v1 = du_n'47'n'8802'0_3278
du_n'47'n'8802'0_3278 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_n'47'n'8802'0_3278
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'62''45'nonZero_136
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Data.Rational.Properties./-cong
d_'47''45'cong_3294 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''45'cong_3294 = erased
-- Data.Rational.Properties./-injective-≃-helper
d_'47''45'injective'45''8771''45'helper_3312 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'47''45'injective'45''8771''45'helper_3312 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6
  = du_'47''45'injective'45''8771''45'helper_3312
du_'47''45'injective'45''8771''45'helper_3312 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'47''45'injective'45''8771''45'helper_3312
  = coe
      MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
      erased
-- Data.Rational.Properties./-injective-≃
d_'47''45'injective'45''8771'_3336 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'47''45'injective'45''8771'_3336 v0 v1 ~v2
  = du_'47''45'injective'45''8771'_3336 v0 v1
du_'47''45'injective'45''8771'_3336 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'47''45'injective'45''8771'_3336 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v2 v3
        -> case coe v2 of
             _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
                 case coe v1 of
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
                     -> case coe v4 of
                          _ | coe geqInt (coe v4) (coe (0 :: Integer)) ->
                              coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30
                          _ -> coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                                 (coe du_'47''45'injective'45''8771''45'helper_3312)
                   _ -> MAlonzo.RTE.mazUnreachableError
             _ -> case coe v1 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
                      -> case coe v4 of
                           _ | coe geqInt (coe v4) (coe (0 :: Integer)) ->
                               coe du_'47''45'injective'45''8771''45'helper_3312
                           _ -> coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30
                    _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.↥ᵘ-toℚᵘ
d_'8613''7512''45'toℚ'7512'_3384 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''7512''45'toℚ'7512'_3384 = erased
-- Data.Rational.Properties.↧ᵘ-toℚᵘ
d_'8615''7512''45'toℚ'7512'_3390 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''7512''45'toℚ'7512'_3390 = erased
-- Data.Rational.Properties.toℚᵘ-injective
d_toℚ'7512''45'injective_3394 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℚ'7512''45'injective_3394 = erased
-- Data.Rational.Properties.fromℚᵘ-injective
d_fromℚ'7512''45'injective_3402 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_fromℚ'7512''45'injective_3402 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (\ v2 ->
            coe du_'47''45'injective'45''8771'_3336 (coe v0) (coe v1)))
-- Data.Rational.Properties.fromℚᵘ-toℚᵘ
d_fromℚ'7512''45'toℚ'7512'_3410 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℚ'7512''45'toℚ'7512'_3410 = erased
-- Data.Rational.Properties.toℚᵘ-fromℚᵘ
d_toℚ'7512''45'fromℚ'7512'_3426 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_toℚ'7512''45'fromℚ'7512'_3426 v0
  = coe
      d_fromℚ'7512''45'injective_3402
      (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
         (coe MAlonzo.Code.Data.Rational.Base.d_fromℚ'7512'_172 (coe v0)))
      v0 erased
-- Data.Rational.Properties.toℚᵘ-cong
d_toℚ'7512''45'cong_3430 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_toℚ'7512''45'cong_3430 ~v0 ~v1 ~v2 = du_toℚ'7512''45'cong_3430
du_toℚ'7512''45'cong_3430 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_toℚ'7512''45'cong_3430
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30
-- Data.Rational.Properties.fromℚᵘ-cong
d_fromℚ'7512''45'cong_3432 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℚ'7512''45'cong_3432 = erased
-- Data.Rational.Properties.toℚᵘ-isRelHomomorphism
d_toℚ'7512''45'isRelHomomorphism_3444 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_toℚ'7512''45'isRelHomomorphism_3444
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsRelHomomorphism'46'constructor_587
      (\ v0 v1 v2 -> coe du_toℚ'7512''45'cong_3430)
-- Data.Rational.Properties.toℚᵘ-isRelMonomorphism
d_toℚ'7512''45'isRelMonomorphism_3446 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64
d_toℚ'7512''45'isRelMonomorphism_3446
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsRelMonomorphism'46'constructor_1563
      (coe d_toℚ'7512''45'isRelHomomorphism_3444) erased
-- Data.Rational.Properties.drop-*≤*
d_drop'45''42''8804''42'_3448 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_drop'45''42''8804''42'_3448 ~v0 ~v1 v2
  = du_drop'45''42''8804''42'_3448 v2
du_drop'45''42''8804''42'_3448 ::
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_drop'45''42''8804''42'_3448 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.toℚᵘ-mono-≤
d_toℚ'7512''45'mono'45''8804'_3452 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_toℚ'7512''45'mono'45''8804'_3452 v0 v1 v2
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (case coe v2 of
            MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v5
              -> coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v5
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Rational.Properties.toℚᵘ-cancel-≤
d_toℚ'7512''45'cancel'45''8804'_3460 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_toℚ'7512''45'cancel'45''8804'_3460 v0 v1 v2
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (case coe v2 of
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v5
              -> coe MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v5
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Rational.Properties.toℚᵘ-isOrderHomomorphism-≤
d_toℚ'7512''45'isOrderHomomorphism'45''8804'_3468 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsOrderHomomorphism_138
d_toℚ'7512''45'isOrderHomomorphism'45''8804'_3468
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsOrderHomomorphism'46'constructor_5435
      (\ v0 v1 v2 -> coe du_toℚ'7512''45'cong_3430)
      (coe d_toℚ'7512''45'mono'45''8804'_3452)
-- Data.Rational.Properties.toℚᵘ-isOrderMonomorphism-≤
d_toℚ'7512''45'isOrderMonomorphism'45''8804'_3470 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsOrderMonomorphism_182
d_toℚ'7512''45'isOrderMonomorphism'45''8804'_3470
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsOrderMonomorphism'46'constructor_9103
      (coe d_toℚ'7512''45'isOrderHomomorphism'45''8804'_3468) erased
      (coe d_toℚ'7512''45'cancel'45''8804'_3460)
-- Data.Rational.Properties.≤-reflexive
d_'8804''45'reflexive_3518 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8804''45'reflexive_3518 v0 ~v1 ~v2
  = du_'8804''45'reflexive_3518 v0
du_'8804''45'reflexive_3518 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'8804''45'reflexive_3518 v0
  = coe
      MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
      (MAlonzo.Code.Data.Integer.Properties.d_'8804''45'refl_2750
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))))
-- Data.Rational.Properties.≤-refl
d_'8804''45'refl_3520 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8804''45'refl_3520 v0 = coe du_'8804''45'reflexive_3518 (coe v0)
-- Data.Rational.Properties.≤-trans
d_'8804''45'trans_3522 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8804''45'trans_3522 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.RelMonomorphism.du_trans_46
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.Structures.du_isRelMonomorphism_218
         (coe d_toℚ'7512''45'isOrderMonomorphism'45''8804'_3470))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'trans_440)
      (coe v0) (coe v1) (coe v2)
-- Data.Rational.Properties.≤-antisym
d_'8804''45'antisym_3524 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_3524 = erased
-- Data.Rational.Properties.≤-total
d_'8804''45'total_3530 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_3530 v0 v1
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
           (coe MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v2))
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
           (coe MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v2))
      (MAlonzo.Code.Data.Integer.Properties.d_'8804''45'total_2776
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))))
-- Data.Rational.Properties._≤?_
d__'8804''63'__3536 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__3536 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (coe MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60)
      (coe du_drop'45''42''8804''42'_3448)
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2794
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))))
-- Data.Rational.Properties._≥?_
d__'8805''63'__3542 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''63'__3542 v0 v1
  = coe d__'8804''63'__3536 (coe v1) (coe v0)
-- Data.Rational.Properties.≤-irrelevant
d_'8804''45'irrelevant_3544 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_3544 = erased
-- Data.Rational.Properties.≤-isPreorder
d_'8804''45'isPreorder_3550 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_3550
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_3518 v0)
      (coe d_'8804''45'trans_3522)
-- Data.Rational.Properties.≤-isTotalPreorder
d_'8804''45'isTotalPreorder_3552 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_'8804''45'isTotalPreorder_3552
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalPreorder'46'constructor_8325
      (coe d_'8804''45'isPreorder_3550) (coe d_'8804''45'total_3530)
-- Data.Rational.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_3554 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_236
d_'8804''45'isPartialOrder_3554
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_11935
      (coe d_'8804''45'isPreorder_3550) erased
-- Data.Rational.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_3556 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_468
d_'8804''45'isTotalOrder_3556
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_22821
      (coe d_'8804''45'isPartialOrder_3554) (coe d_'8804''45'total_3530)
-- Data.Rational.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_3558 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_524
d_'8804''45'isDecTotalOrder_3558
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_24961
      (coe d_'8804''45'isTotalOrder_3556) (coe d__'8799'__2706)
      (coe d__'8804''63'__3536)
-- Data.Rational.Properties.≤-totalPreorder
d_'8804''45'totalPreorder_3560 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_232
d_'8804''45'totalPreorder_3560
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalPreorder'46'constructor_4405
      d_'8804''45'isTotalPreorder_3552
-- Data.Rational.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_3562 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076
d_'8804''45'decTotalOrder_3562
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_21007
      d_'8804''45'isDecTotalOrder_3558
-- Data.Rational.Properties.drop-*<*
d_drop'45''42''60''42'_3564 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_drop'45''42''60''42'_3564 ~v0 ~v1 v2
  = du_drop'45''42''60''42'_3564 v2
du_drop'45''42''60''42'_3564 ::
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_drop'45''42''60''42'_3564 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.toℚᵘ-mono-<
d_toℚ'7512''45'mono'45''60'_3568 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_toℚ'7512''45'mono'45''60'_3568 v0 v1 v2
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (case coe v2 of
            MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v5
              -> coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v5
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Rational.Properties.toℚᵘ-cancel-<
d_toℚ'7512''45'cancel'45''60'_3576 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_toℚ'7512''45'cancel'45''60'_3576 v0 v1 v2
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (case coe v2 of
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v5
              -> coe MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v5
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Rational.Properties.toℚᵘ-isOrderHomomorphism-<
d_toℚ'7512''45'isOrderHomomorphism'45''60'_3584 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsOrderHomomorphism_138
d_toℚ'7512''45'isOrderHomomorphism'45''60'_3584
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsOrderHomomorphism'46'constructor_5435
      (\ v0 v1 v2 -> coe du_toℚ'7512''45'cong_3430)
      (coe d_toℚ'7512''45'mono'45''60'_3568)
-- Data.Rational.Properties.toℚᵘ-isOrderMonomorphism-<
d_toℚ'7512''45'isOrderMonomorphism'45''60'_3586 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsOrderMonomorphism_182
d_toℚ'7512''45'isOrderMonomorphism'45''60'_3586
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsOrderMonomorphism'46'constructor_9103
      (coe d_toℚ'7512''45'isOrderHomomorphism'45''60'_3584) erased
      (coe d_toℚ'7512''45'cancel'45''60'_3576)
-- Data.Rational.Properties.<⇒≤
d_'60''8658''8804'_3588 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'60''8658''8804'_3588 ~v0 ~v1 v2 = du_'60''8658''8804'_3588 v2
du_'60''8658''8804'_3588 ::
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'60''8658''8804'_3588 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v3
        -> coe
             MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
             (coe
                MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.≮⇒≥
d_'8814''8658''8805'_3592 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8814''8658''8805'_3592 v0 v1 ~v2
  = du_'8814''8658''8805'_3592 v0 v1
du_'8814''8658''8805'_3592 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'8814''8658''8805'_3592 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8814''8658''8805'_2922
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))))
-- Data.Rational.Properties.≰⇒>
d_'8816''8658''62'_3600 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'8816''8658''62'_3600 v0 v1 ~v2 = du_'8816''8658''62'_3600 v0 v1
du_'8816''8658''62'_3600 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'8816''8658''62'_3600 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8816''8658''62'_2896
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))))
-- Data.Rational.Properties.<⇒≢
d_'60''8658''8802'_3608 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_3608 = erased
-- Data.Rational.Properties.<-irrefl
d_'60''45'irrefl_3616 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_3616 = erased
-- Data.Rational.Properties.<-asym
d_'60''45'asym_3620 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_3620 = erased
-- Data.Rational.Properties.<-dense
d_'60''45'dense_3626 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'dense_3626 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.Rational.Base.d_fromℚ'7512'_172
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
               (coe
                  d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2)))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            d_toℚ'7512''45'cancel'45''60'_3576 (coe v0)
            (coe
               MAlonzo.Code.Data.Rational.Base.d_fromℚ'7512'_172
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe
                        d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2)))))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'691''45''8771'_734
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2))))
               (coe
                  MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d_fromℚ'7512'_172
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                           (coe
                              d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2))))))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                  (coe
                     d_toℚ'7512''45'fromℚ'7512'_3426
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                           (coe
                              d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2))))))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                        (coe
                           d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2)))))))
         (coe
            d_toℚ'7512''45'cancel'45''60'_3576
            (coe
               MAlonzo.Code.Data.Rational.Base.d_fromℚ'7512'_172
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe
                        d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2)))))
            (coe v1)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'737''45''8771'_770
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2))))
               (coe
                  MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d_fromℚ'7512'_172
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                           (coe
                              d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2))))))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                  (coe
                     d_toℚ'7512''45'fromℚ'7512'_3426
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                           (coe
                              d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2))))))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'dense_592
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                        (coe
                           d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v2))))))))
-- Data.Rational.Properties.<-≤-trans
d_'60''45''8804''45'trans_3646 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'60''45''8804''45'trans_3646 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v7
        -> case coe v4 of
             MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v10
               -> coe
                    MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''60''45'nonNeg_6284
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                          (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v2)))
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v2))
                          (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0)))
                       (addInt
                          (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Data.Rational.Base.d_denominator'45'1_16 (coe v1)))
                       (let v11
                              = coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                        coe
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                             (coe v11)
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                   (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v2)))
                                (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v2))
                                   (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0)))
                                (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                (\ v12 v13 v14 v15 v16 -> v16)
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v2)))
                                   (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v2))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                         (coe v1))))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v2))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0)))
                                   (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                   (\ v12 v13 v14 v15 v16 -> v16)
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v1))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v2))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v2))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v0)))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                      (\ v12 v13 v14 v15 v16 -> v16)
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v1))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v2))))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v1)))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v2)))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                               (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v1)))
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                            (\ v12 v13 v14 v15 v16 ->
                                               coe
                                                 MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                                 v15 v16)
                                            (coe
                                               MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                            (\ v12 v13 v14 v15 v16 ->
                                               coe
                                                 MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                                 v15 v16))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v2))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v1)))
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                            (\ v12 v13 v14 v15 v16 -> v16)
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                     (coe v1))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                     (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                               (\ v12 v13 v14 v15 v16 -> v16)
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                        (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v2)))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                        (coe v1))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v2))))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                        (coe v2))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0)))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                                     (\ v12 v13 v14 v15 v16 ->
                                                        coe
                                                          MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                                          v15 v16))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v2))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v1))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v0)))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                     (\ v12 v13 v14 v15 v16 -> v16)
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                              (coe v2))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v1))))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                              (coe v2)))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v1)))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                              (coe v2))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v0)))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v1)))
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                        (\ v12 v13 v14 v15 v16 -> v16)
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                                 (coe v2)))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v1)))
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                                 (coe v2))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                 (coe v0)))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v1)))
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                                 (coe v2))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                 (coe v0)))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v1)))
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                 (coe
                                                                    MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                                    (coe v2))
                                                                 (coe
                                                                    MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                    (coe v0)))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                 (coe v1))))
                                                        erased)
                                                     erased)
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'737''45''8804''45'nonNeg_6076
                                                     (MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v2)))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v1)))
                                                     v10))
                                               erased)
                                            erased)
                                         (coe
                                            MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''60''45'pos_6226
                                            (MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v2))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v1)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v0)))
                                            v7))
                                      erased)
                                   erased)
                                erased))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.≤-<-trans
d_'8804''45''60''45'trans_3680 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'8804''45''60''45'trans_3680 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v7
        -> case coe v4 of
             MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v10
               -> coe
                    MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''60''45'nonNeg_6284
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                          (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v2)))
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v2))
                          (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0)))
                       (addInt
                          (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Data.Rational.Base.d_denominator'45'1_16 (coe v1)))
                       (let v11
                              = coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                        coe
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                             (coe v11)
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                   (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v2)))
                                (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v2))
                                   (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0)))
                                (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                (\ v12 v13 v14 v15 v16 -> v16)
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v2)))
                                   (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v2))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                         (coe v1))))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v2))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0)))
                                   (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                   (\ v12 v13 v14 v15 v16 -> v16)
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v1))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v2))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v2))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v0)))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                      (\ v12 v13 v14 v15 v16 -> v16)
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v1))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v2))))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v1)))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v2)))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                               (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                            (coe v1)))
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                            (coe
                                               MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                            (\ v12 v13 v14 v15 v16 ->
                                               coe
                                                 MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                                 v15 v16))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v2))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v1)))
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                            (\ v12 v13 v14 v15 v16 -> v16)
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                     (coe v1))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                     (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                               (\ v12 v13 v14 v15 v16 -> v16)
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                        (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v2)))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                        (coe v1))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v2))))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                        (coe v2))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0)))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                     (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                                     (\ v12 v13 v14 v15 v16 ->
                                                        coe
                                                          MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                                          v15 v16)
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                                     (\ v12 v13 v14 v15 v16 ->
                                                        coe
                                                          MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                                          v15 v16))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v2))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v1))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v0)))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                     (\ v12 v13 v14 v15 v16 -> v16)
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                              (coe v2))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v1))))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                              (coe v2)))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v1)))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                              (coe v2))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v0)))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v1)))
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                        (\ v12 v13 v14 v15 v16 -> v16)
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                                 (coe v2)))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v1)))
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                                 (coe v2))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                 (coe v0)))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v1)))
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                                 (coe v2))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                 (coe v0)))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                              (coe v1)))
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                 (coe
                                                                    MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                                    (coe v2))
                                                                 (coe
                                                                    MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                    (coe v0)))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                                 (coe v1))))
                                                        erased)
                                                     erased)
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'737''45''60''45'pos_6194
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v2)))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                           (coe v1)))
                                                     (coe v10)))
                                               erased)
                                            erased)
                                         (coe
                                            MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''8804''45'nonNeg_6034
                                            (coe
                                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                               (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                                  (coe v0)))
                                            (coe v7)))
                                      erased)
                                   erased)
                                erased))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.<-trans
d_'60''45'trans_3714 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'60''45'trans_3714 v0 v1 v2 v3
  = coe
      d_'8804''45''60''45'trans_3680 (coe v0) (coe v1) (coe v2)
      (coe du_'60''8658''8804'_3588 (coe v3))
-- Data.Rational.Properties._<?_
d__'60''63'__3718 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__3718 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (coe MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68)
      (coe du_drop'45''42''60''42'_3564)
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3104
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
            (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))))
-- Data.Rational.Properties._>?_
d__'62''63'__3724 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''63'__3724 v0 v1 = coe d__'60''63'__3718 (coe v1) (coe v0)
-- Data.Rational.Properties.<-cmp
d_'60''45'cmp_3726 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_3726 v0 v1
  = let v2
          = MAlonzo.Code.Data.Integer.Properties.d_'60''45'cmp_3014
              (coe
                 MAlonzo.Code.Data.Integer.Base.d__'9667'__230
                 (coe
                    MAlonzo.Code.Data.Sign.Base.d__'42'__14
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_sign_24
                       (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0)))
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_sign_24
                       (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1))))
                 (coe
                    mulInt
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                       (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0)))
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                       (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))))
              (coe
                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                 (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
                 (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v3
           -> coe
                MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                (coe MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v3)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v4
           -> coe
                MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                (coe MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Rational.Properties.<-irrelevant
d_'60''45'irrelevant_3766 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_3766 = erased
-- Data.Rational.Properties.<-respʳ-≡
d_'60''45'resp'691''45''8801'_3772 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'60''45'resp'691''45''8801'_3772 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''45'resp'691''45''8801'_3772 v4
du_'60''45'resp'691''45''8801'_3772 ::
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'60''45'resp'691''45''8801'_3772 v0 = coe v0
-- Data.Rational.Properties.<-respˡ-≡
d_'60''45'resp'737''45''8801'_3776 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'60''45'resp'737''45''8801'_3776 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''45'resp'737''45''8801'_3776 v4
du_'60''45'resp'737''45''8801'_3776 ::
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'60''45'resp'737''45''8801'_3776 v0 = coe v0
-- Data.Rational.Properties.<-resp-≡
d_'60''45'resp'45''8801'_3780 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8801'_3780
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_3782 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_354
d_'60''45'isStrictPartialOrder_3782
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_16311
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      d_'60''45'trans_3714 d_'60''45'resp'45''8801'_3780
-- Data.Rational.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_3784 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_600
d_'60''45'isStrictTotalOrder_3784
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_27253
      (coe d_'60''45'isStrictPartialOrder_3782) (coe d_'60''45'cmp_3726)
-- Data.Rational.Properties.<-isDenseLinearOrder
d_'60''45'isDenseLinearOrder_3786 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDenseLinearOrder_660
d_'60''45'isDenseLinearOrder_3786
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDenseLinearOrder'46'constructor_30431
      (coe d_'60''45'isStrictTotalOrder_3784) (coe d_'60''45'dense_3626)
-- Data.Rational.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_3788 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_744
d_'60''45'strictPartialOrder_3788
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_14243
      d_'60''45'isStrictPartialOrder_3782
-- Data.Rational.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_3790 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1256
d_'60''45'strictTotalOrder_3790
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_24345
      d_'60''45'isStrictTotalOrder_3784
-- Data.Rational.Properties.<-denseLinearOrder
d_'60''45'denseLinearOrder_3792 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DenseLinearOrder_1368
d_'60''45'denseLinearOrder_3792
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DenseLinearOrder'46'constructor_26715
      d_'60''45'isDenseLinearOrder_3786
-- Data.Rational.Properties.≤-Reasoning.Triple._IsRelatedTo_
d__IsRelatedTo__3798 a0 a1 = ()
-- Data.Rational.Properties.≤-Reasoning.Triple._∎
d__'8718'_3800 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_3800
  = let v0 = d_'8804''45'isPreorder_3550 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
            (coe v0)))
-- Data.Rational.Properties.≤-Reasoning.Triple.<-go
d_'60''45'go_3802 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_3802
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
      (coe d_'60''45'trans_3714)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
      (coe d_'60''45''8804''45'trans_3646)
-- Data.Rational.Properties.≤-Reasoning.Triple.IsEquality
d_IsEquality_3804 a0 a1 a2 = ()
-- Data.Rational.Properties.≤-Reasoning.Triple.IsEquality?
d_IsEquality'63'_3806 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_3806 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
      v2
-- Data.Rational.Properties.≤-Reasoning.Triple.IsStrict
d_IsStrict_3808 a0 a1 a2 = ()
-- Data.Rational.Properties.≤-Reasoning.Triple.IsStrict?
d_IsStrict'63'_3810 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_3810 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
      v2
-- Data.Rational.Properties.≤-Reasoning.Triple.begin_
d_begin__3812 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_begin__3812
  = let v0 = d_'8804''45'isPreorder_3550 in
    coe
      (let v1 = \ v1 v2 v3 -> coe du_'60''8658''8804'_3588 v3 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe v0) (coe v1))))
-- Data.Rational.Properties.≤-Reasoning.Triple.begin-contradiction_
d_begin'45'contradiction__3814 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d_begin'45'contradiction__3814 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
-- Data.Rational.Properties.≤-Reasoning.Triple.begin_
d_begin__3816 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__3816 = erased
-- Data.Rational.Properties.≤-Reasoning.Triple.begin_
d_begin__3818 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_begin__3818
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Data.Rational.Properties.≤-Reasoning.Triple.eqRelation
d_eqRelation_3820 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_3820
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
-- Data.Rational.Properties.≤-Reasoning.Triple.extractEquality
d_extractEquality_3824 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractEquality_3824 = erased
-- Data.Rational.Properties.≤-Reasoning.Triple.extractStrict
d_extractStrict_3826 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_extractStrict_3826 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
      v2 v3
-- Data.Rational.Properties.≤-Reasoning.Triple.start
d_start_3834 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_start_3834
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
      (coe d_'8804''45'isPreorder_3550)
      (\ v0 v1 v2 -> coe du_'60''8658''8804'_3588 v2)
-- Data.Rational.Properties.≤-Reasoning.Triple.step-<
d_step'45''60'_3836 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_3836
  = let v0 = d_'60''45'trans_3714 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160 in
       coe
         (let v2 = d_'60''45''8804''45'trans_3646 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe v0) (coe v1) (coe v2)))))
-- Data.Rational.Properties.≤-Reasoning.Triple.step-≡
d_step'45''8801'_3846 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_3846
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Properties.≤-Reasoning.Triple.step-≡-∣
d_step'45''8801''45''8739'_3848 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_3848 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_3848 v2
du_step'45''8801''45''8739'_3848 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_3848 v0 = coe v0
-- Data.Rational.Properties.≤-Reasoning.Triple.step-≡-⟨
d_step'45''8801''45''10216'_3850 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_3850
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Properties.≤-Reasoning.Triple.step-≡-⟩
d_step'45''8801''45''10217'_3852 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_3852
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Properties.≤-Reasoning.Triple.step-≡˘
d_step'45''8801''728'_3854 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_3854
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Properties.≤-Reasoning.Triple.step-≤
d_step'45''8804'_3856 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_3856
  = let v0 = d_'8804''45'isPreorder_3550 in
    coe
      (let v1 = d_'8804''45''60''45'trans_3680 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe v0) (coe v1))))
-- Data.Rational.Properties.≤-Reasoning.Triple.stop
d_stop_3858 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_3858
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
      (coe d_'8804''45'isPreorder_3550)
-- Data.Rational.Properties.≤-Reasoning.Triple.strictRelation
d_strictRelation_3862 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_3862
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
-- Data.Rational.Properties.≤-Reasoning.Triple.≈-go
d_'8776''45'go_3864 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_3864
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
      (coe d_'8804''45'isPreorder_3550)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
-- Data.Rational.Properties.≤-Reasoning.Triple.≡-go
d_'8801''45'go_3866 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_3866 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_3866 v4
du_'8801''45'go_3866 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_3866 v0 = coe v0
-- Data.Rational.Properties.≤-Reasoning.Triple.≤-go
d_'8804''45'go_3868 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_3868
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
      (coe d_'8804''45'isPreorder_3550)
      (coe d_'8804''45''60''45'trans_3680)
-- Data.Rational.Properties.≤-Reasoning.≃-go
d_'8771''45'go_3886 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8771''45'go_3886 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
         (coe d_'8804''45'isPreorder_3550)
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
         (coe v0) (coe v1) (coe v2))
      erased
-- Data.Rational.Properties.≤-Reasoning._.step-≃-⟨
d_step'45''8771''45''10216'_3894 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8771''45''10216'_3894
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
      (coe d_'8771''45'go_3886) (\ v0 v1 -> coe du_'8771''45'sym_2856)
-- Data.Rational.Properties.≤-Reasoning._.step-≃-⟩
d_step'45''8771''45''10217'_3896 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Base.T__'8771'__40 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8771''45''10217'_3896
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
      (coe d_'8771''45'go_3886)
-- Data.Rational.Properties.positive⁻¹
d_positive'8315''185'_3900 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_positive'8315''185'_3900 v0 ~v1 = du_positive'8315''185'_3900 v0
du_positive'8315''185'_3900 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_positive'8315''185'_3900 v0
  = coe
      d_toℚ'7512''45'cancel'45''60'_3576
      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_positive'8315''185'_926
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
-- Data.Rational.Properties.nonNegative⁻¹
d_nonNegative'8315''185'_3906 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_nonNegative'8315''185'_3906 v0 ~v1
  = du_nonNegative'8315''185'_3906 v0
du_nonNegative'8315''185'_3906 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_nonNegative'8315''185'_3906 v0
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460
      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_nonNegative'8315''185'_932
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
-- Data.Rational.Properties.negative⁻¹
d_negative'8315''185'_3912 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_negative'8315''185'_3912 v0 ~v1 = du_negative'8315''185'_3912 v0
du_negative'8315''185'_3912 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_negative'8315''185'_3912 v0
  = coe
      d_toℚ'7512''45'cancel'45''60'_3576 (coe v0)
      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_negative'8315''185'_938
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
-- Data.Rational.Properties.nonPositive⁻¹
d_nonPositive'8315''185'_3918 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_nonPositive'8315''185'_3918 v0 ~v1
  = du_nonPositive'8315''185'_3918 v0
du_nonPositive'8315''185'_3918 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_nonPositive'8315''185'_3918 v0
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460 (coe v0)
      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_nonPositive'8315''185'_944
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
-- Data.Rational.Properties.neg<pos
d_neg'60'pos_3926 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_neg'60'pos_3926 v0 v1 ~v2 ~v3 = du_neg'60'pos_3926 v0 v1
du_neg'60'pos_3926 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_neg'60'pos_3926 v0 v1
  = coe
      d_toℚ'7512''45'cancel'45''60'_3576 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_neg'60'pos_964
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
-- Data.Rational.Properties.neg-antimono-<
d_neg'45'antimono'45''60'_3932 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_neg'45'antimono'45''60'_3932 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             0 -> case coe v1 of
                    MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v6 v7
                      -> case coe v2 of
                           MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v11
                             -> case coe v6 of
                                  0 -> case coe v11 of
                                         MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v14
                                           -> coe
                                                MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                                                   v14)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> coe
                                         seq (coe v11)
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
                                            (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   seq (coe v1)
                   (case coe v2 of
                      MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v8
                        -> case coe v8 of
                             MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v11
                               -> case coe v11 of
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v14
                                      -> coe
                                           MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v14)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> case coe v1 of
                    MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v6 v7
                      -> case coe v6 of
                           0 -> case coe v2 of
                                  MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v11
                                    -> coe
                                         seq (coe v11)
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                                               (coe
                                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                  (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ | coe geqInt (coe v6) (coe (1 :: Integer)) ->
                               case coe v2 of
                                 MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v11
                                   -> coe
                                        seq (coe v11)
                                        (coe
                                           MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
                                           (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> case coe v2 of
                                  MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v14
                                           -> coe
                                                MAlonzo.Code.Data.Rational.Base.C_'42''60''42'_68
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v14))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.neg-antimono-≤
d_neg'45'antimono'45''8804'_3942 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_neg'45'antimono'45''8804'_3942 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             0 -> case coe v1 of
                    MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v6 v7
                      -> case coe v2 of
                           MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v11
                             -> case coe v6 of
                                  0 -> case coe v11 of
                                         MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v14
                                           -> coe
                                                MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                                                   v14)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> coe
                                         seq (coe v11)
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   seq (coe v1)
                   (case coe v2 of
                      MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v8
                        -> case coe v8 of
                             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v11
                               -> case coe v11 of
                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v14
                                      -> coe
                                           MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                                              v14)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError
                      _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> case coe v1 of
                    MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v6 v7
                      -> case coe v6 of
                           0 -> case coe v2 of
                                  MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v11
                                    -> coe
                                         seq (coe v11)
                                         (coe
                                            MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                                               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ | coe geqInt (coe v6) (coe (1 :: Integer)) ->
                               case coe v2 of
                                 MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v11
                                   -> coe
                                        seq (coe v11)
                                        (coe
                                           MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
                                           (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> case coe v2 of
                                  MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v14
                                           -> coe
                                                MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v14))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.≤ᵇ⇒≤
d_'8804''7495''8658''8804'_3952 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  AgdaAny -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8804''7495''8658''8804'_3952 v0 v1
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60)
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Integer.Properties.du_'8804''7495''8658''8804'_2842
           (coe
              MAlonzo.Code.Data.Integer.Base.d__'42'__308
              (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
              (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
           (coe
              MAlonzo.Code.Data.Integer.Base.d__'42'__308
              (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
              (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))))
-- Data.Rational.Properties.≤⇒≤ᵇ
d_'8804''8658''8804''7495'_3954 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 -> AgdaAny
d_'8804''8658''8804''7495'_3954 ~v0 ~v1
  = du_'8804''8658''8804''7495'_3954
du_'8804''8658''8804''7495'_3954 ::
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 -> AgdaAny
du_'8804''8658''8804''7495'_3954
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8804''8658''8804''7495'_2850)
      (coe du_drop'45''42''8804''42'_3448)
-- Data.Rational.Properties.↥+ᵘ
d_'8613''43''7512'_3956 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 -> Integer
d_'8613''43''7512'_3956 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'43'__276
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
         (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1))
         (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0)))
-- Data.Rational.Properties.↧+ᵘ
d_'8615''43''7512'_3962 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 -> Integer
d_'8615''43''7512'_3962 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))
      (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1))
-- Data.Rational.Properties.+-nf
d_'43''45'nf_3968 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 -> Integer
d_'43''45'nf_3968 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.GCD.d_gcd_136
      (coe d_'8613''43''7512'_3956 (coe v0) (coe v1))
      (coe d_'8615''43''7512'_3962 (coe v0) (coe v1))
-- Data.Rational.Properties.↥-+
d_'8613''45''43'_3978 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''45''43'_3978 = erased
-- Data.Rational.Properties.↧-+
d_'8615''45''43'_3988 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''45''43'_3988 = erased
-- Data.Rational.Properties._.Homomorphic₁
d_Homomorphic'8321'_3998 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  ()
d_Homomorphic'8321'_3998 = erased
-- Data.Rational.Properties._.Homomorphic₂
d_Homomorphic'8322'_4000 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  ()
d_Homomorphic'8322'_4000 = erased
-- Data.Rational.Properties.toℚᵘ-homo-+
d_toℚ'7512''45'homo'45''43'_4004 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_toℚ'7512''45'homo'45''43'_4004 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6
               -> let v8
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased erased
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710
                               (coe
                                  MAlonzo.Code.Data.Nat.GCD.d_gcd_152
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                     (coe
                                        d_'8613''43''7512'_3956
                                        (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3)
                                        (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6)))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                     (coe
                                        d_'8615''43''7512'_3962
                                        (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3)
                                        (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6))))
                               (coe (0 :: Integer))) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> coe
                              seq (coe v9)
                              (coe
                                 seq (coe v10)
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties._.eq2
d_eq2_4024 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq2_4024 = erased
-- Data.Rational.Properties._.eq
d_eq_4026 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_4026 = erased
-- Data.Rational.Properties.toℚᵘ-isMagmaHomomorphism-+
d_toℚ'7512''45'isMagmaHomomorphism'45''43'_4158 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_188
d_toℚ'7512''45'isMagmaHomomorphism'45''43'_4158
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMagmaHomomorphism'46'constructor_4629
      (coe d_toℚ'7512''45'isRelHomomorphism_3444)
      (coe d_toℚ'7512''45'homo'45''43'_4004)
-- Data.Rational.Properties.toℚᵘ-isMonoidHomomorphism-+
d_toℚ'7512''45'isMonoidHomomorphism'45''43'_4160 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_362
d_toℚ'7512''45'isMonoidHomomorphism'45''43'_4160
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidHomomorphism'46'constructor_9411
      (coe d_toℚ'7512''45'isMagmaHomomorphism'45''43'_4158)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'refl_166)
-- Data.Rational.Properties.toℚᵘ-isMonoidMonomorphism-+
d_toℚ'7512''45'isMonoidMonomorphism'45''43'_4162 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384
d_toℚ'7512''45'isMonoidMonomorphism'45''43'_4162
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidMonomorphism'46'constructor_10237
      (coe d_toℚ'7512''45'isMonoidHomomorphism'45''43'_4160) erased
-- Data.Rational.Properties.toℚᵘ-homo‿-
d_toℚ'7512''45'homo'8255''45'_4164 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_toℚ'7512''45'homo'8255''45'_4164 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.toℚᵘ-isGroupHomomorphism-+
d_toℚ'7512''45'isGroupHomomorphism'45''43'_4166 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsGroupHomomorphism_634
d_toℚ'7512''45'isGroupHomomorphism'45''43'_4166
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsGroupHomomorphism'46'constructor_14585
      (coe d_toℚ'7512''45'isMonoidHomomorphism'45''43'_4160)
      (coe d_toℚ'7512''45'homo'8255''45'_4164)
-- Data.Rational.Properties.toℚᵘ-isGroupMonomorphism-+
d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsGroupMonomorphism_660
d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsGroupMonomorphism'46'constructor_15537
      (coe d_toℚ'7512''45'isGroupHomomorphism'45''43'_4166) erased
-- Data.Rational.Properties.+-assoc
d_'43''45'assoc_4226 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_4226 = erased
-- Data.Rational.Properties.+-comm
d_'43''45'comm_4228 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_4228 = erased
-- Data.Rational.Properties.+-identityˡ
d_'43''45'identity'737'_4230 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737'_4230 = erased
-- Data.Rational.Properties.+-identityʳ
d_'43''45'identity'691'_4232 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_4232 = erased
-- Data.Rational.Properties.+-identity
d_'43''45'identity_4234 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'identity_4234
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Rational.Properties.+-inverseˡ
d_'43''45'inverse'737'_4236 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'737'_4236 = erased
-- Data.Rational.Properties.+-inverseʳ
d_'43''45'inverse'691'_4238 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'691'_4238 = erased
-- Data.Rational.Properties.+-inverse
d_'43''45'inverse_4240 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_4240
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_inverse_206
      (coe MAlonzo.Code.Data.Rational.Base.d_'43''45'0'45'rawGroup_370)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45'0'45'rawGroup_290)
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'isMagma_1642)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'inverse_1214)
-- Data.Rational.Properties.-‿cong
d_'45''8255'cong_4242 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45''8255'cong_4242 = erased
-- Data.Rational.Properties.neg-distrib-+
d_neg'45'distrib'45''43'_4248 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'45''43'_4248 = erased
-- Data.Rational.Properties.+-isMagma
d_'43''45'isMagma_4250 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'43''45'isMagma_4250
  = let v0
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128
              (coe
                 MAlonzo.Code.Data.Rational.Base.d_'43''45'0'45'rawGroup_370) in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128
                 (coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45'0'45'rawGroup_290) in
       coe
         (let v2 = MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 in
          coe
            (let v3
                   = coe
                       MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                       (coe d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isMagma_238
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
                  (coe v2)
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                     (coe v3))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'isMagma_1642)))))
-- Data.Rational.Properties.+-isSemigroup
d_'43''45'isSemigroup_4252 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'43''45'isSemigroup_4252
  = let v0
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128
              (coe
                 MAlonzo.Code.Data.Rational.Base.d_'43''45'0'45'rawGroup_370) in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128
                 (coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45'0'45'rawGroup_290) in
       coe
         (let v2 = MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 in
          coe
            (let v3
                   = coe
                       MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                       (coe d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSemigroup_268
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
                  (coe v2)
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                     (coe v3))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'isSemigroup_1644)))))
-- Data.Rational.Properties.+-0-isMonoid
d_'43''45'0'45'isMonoid_4254 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'43''45'0'45'isMonoid_4254
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isMonoid_192
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128
         (coe MAlonzo.Code.Data.Rational.Base.d_'43''45'0'45'rawGroup_370))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45'0'45'rawGroup_290))
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
         (coe d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'0'45'isMonoid_1646)
-- Data.Rational.Properties.+-0-isCommutativeMonoid
d_'43''45'0'45'isCommutativeMonoid_4256 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'0'45'isCommutativeMonoid_4256
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isCommutativeMonoid_236
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128
         (coe MAlonzo.Code.Data.Rational.Base.d_'43''45'0'45'rawGroup_370))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45'0'45'rawGroup_290))
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
         (coe d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'0'45'isCommutativeMonoid_1648)
-- Data.Rational.Properties.+-0-isGroup
d_'43''45'0'45'isGroup_4258 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_'43''45'0'45'isGroup_4258
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_isGroup_350
      (coe MAlonzo.Code.Data.Rational.Base.d_'43''45'0'45'rawGroup_370)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45'0'45'rawGroup_290)
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'0'45'isGroup_1650)
-- Data.Rational.Properties.+-0-isAbelianGroup
d_'43''45'0'45'isAbelianGroup_4260 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
d_'43''45'0'45'isAbelianGroup_4260
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_isAbelianGroup_418
      (coe MAlonzo.Code.Data.Rational.Base.d_'43''45'0'45'rawGroup_370)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45'0'45'rawGroup_290)
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe d_toℚ'7512''45'isGroupMonomorphism'45''43'_4168)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'0'45'isAbelianGroup_1652)
-- Data.Rational.Properties.+-magma
d_'43''45'magma_4262 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'43''45'magma_4262
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1323
      MAlonzo.Code.Data.Rational.Base.d__'43'__270 d_'43''45'isMagma_4250
-- Data.Rational.Properties.+-semigroup
d_'43''45'semigroup_4264 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'43''45'semigroup_4264
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9837
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      d_'43''45'isSemigroup_4252
-- Data.Rational.Properties.+-0-monoid
d_'43''45'0'45'monoid_4266 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'43''45'0'45'monoid_4266
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16201
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      d_'43''45'0'45'isMonoid_4254
-- Data.Rational.Properties.+-0-commutativeMonoid
d_'43''45'0'45'commutativeMonoid_4268 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''45'0'45'commutativeMonoid_4268
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      d_'43''45'0'45'isCommutativeMonoid_4256
-- Data.Rational.Properties.+-0-group
d_'43''45'0'45'group_4270 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1524
d_'43''45'0'45'group_4270
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Group'46'constructor_27347
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      MAlonzo.Code.Data.Rational.Base.d_'45'__112
      d_'43''45'0'45'isGroup_4258
-- Data.Rational.Properties.+-0-abelianGroup
d_'43''45'0'45'abelianGroup_4272 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1640
d_'43''45'0'45'abelianGroup_4272
  = coe
      MAlonzo.Code.Algebra.Bundles.C_AbelianGroup'46'constructor_29899
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      MAlonzo.Code.Data.Rational.Base.d_'45'__112
      d_'43''45'0'45'isAbelianGroup_4260
-- Data.Rational.Properties.+-mono-≤
d_'43''45'mono'45''8804'_4274 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'43''45'mono'45''8804'_4274 v0 v1 v2 v3 v4 v5
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'60''8658''8804'_556
                 v8))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v2)))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v2)))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
            (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45''60''45'trans_610))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v3)))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v3)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3))))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                     (coe d_toℚ'7512''45'homo'45''43'_4004 (coe v1) (coe v3))))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'mono'45''8804'_1350
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v3))
                  (d_toℚ'7512''45'mono'45''8804'_3452 (coe v0) (coe v1) (coe v4))
                  (d_toℚ'7512''45'mono'45''8804'_3452 (coe v2) (coe v3) (coe v5))))
            (d_toℚ'7512''45'homo'45''43'_4004 (coe v0) (coe v2))))
-- Data.Rational.Properties.+-monoˡ-≤
d_'43''45'mono'737''45''8804'_4292 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'43''45'mono'737''45''8804'_4292 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''8804'_4274 (coe v1) (coe v2) (coe v0) (coe v0)
      (coe v3) (coe d_'8804''45'refl_3520 (coe v0))
-- Data.Rational.Properties.+-monoʳ-≤
d_'43''45'mono'691''45''8804'_4298 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'43''45'mono'691''45''8804'_4298 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''8804'_4274 (coe v0) (coe v0) (coe v1) (coe v2)
      (coe d_'8804''45'refl_3520 (coe v0)) (coe v3)
-- Data.Rational.Properties.nonNeg+nonNeg⇒nonNeg
d_nonNeg'43'nonNeg'8658'nonNeg_4312 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_nonNeg'43'nonNeg'8658'nonNeg_4312 v0 ~v1 v2 ~v3
  = du_nonNeg'43'nonNeg'8658'nonNeg_4312 v0 v2
du_nonNeg'43'nonNeg'8658'nonNeg_4312 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_nonNeg'43'nonNeg'8658'nonNeg_4312 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_nonNegative_264
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))
      (coe
         d_'43''45'mono'45''8804'_4274
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v0)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
         (coe du_nonNegative'8315''185'_3906 (coe v0))
         (coe du_nonNegative'8315''185'_3906 (coe v1)))
-- Data.Rational.Properties.nonPos+nonPos⇒nonPos
d_nonPos'43'nonPos'8658'nonPos_4326 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
d_nonPos'43'nonPos'8658'nonPos_4326 v0 ~v1 v2 ~v3
  = du_nonPos'43'nonPos'8658'nonPos_4326 v0 v2
du_nonPos'43'nonPos'8658'nonPos_4326 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
du_nonPos'43'nonPos'8658'nonPos_4326 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_nonPositive_256
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))
      (coe
         d_'43''45'mono'45''8804'_4274 (coe v0)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
         (coe du_nonPositive'8315''185'_3918 (coe v0))
         (coe du_nonPositive'8315''185'_3918 (coe v1)))
-- Data.Rational.Properties.+-mono-<-≤
d_'43''45'mono'45''60''45''8804'_4332 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'43''45'mono'45''60''45''8804'_4332 v0 v1 v2 v3 v4 v5
  = coe
      d_toℚ'7512''45'cancel'45''60'_3576
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3))
      (let v6
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v6)
            (coe
               MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v2)))
            (coe
               MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v2)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'trans_678)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45''8804''45'trans_644))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v3)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v3)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3))))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                        (coe d_toℚ'7512''45'homo'45''43'_4004 (coe v1) (coe v3))))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'mono'45''60''45''8804'_1460
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v3))
                     (coe d_toℚ'7512''45'mono'45''60'_3568 (coe v0) (coe v1) (coe v4))
                     (coe
                        d_toℚ'7512''45'mono'45''8804'_3452 (coe v2) (coe v3) (coe v5))))
               (d_toℚ'7512''45'homo'45''43'_4004 (coe v0) (coe v2)))))
-- Data.Rational.Properties.+-mono-≤-<
d_'43''45'mono'45''8804''45''60'_4350 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'43''45'mono'45''8804''45''60'_4350 v0 v1 v2 v3 v4 v5
  = coe
      d_'43''45'mono'45''60''45''8804'_4332 (coe v2) (coe v3) (coe v0)
      (coe v1) (coe v5) (coe v4)
-- Data.Rational.Properties.+-mono-<
d_'43''45'mono'45''60'_4372 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'43''45'mono'45''60'_4372 v0 v1 v2 v3 v4 v5
  = coe
      d_'60''45'trans_3714
      (MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v2))
      (MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v2))
      (MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1) (coe v3))
      (d_'43''45'mono'45''60''45''8804'_4332
         (coe v0) (coe v1) (coe v2) (coe v2) (coe v4)
         (coe d_'8804''45'refl_3520 (coe v2)))
      (d_'43''45'mono'45''8804''45''60'_4350
         (coe v1) (coe v1) (coe v2) (coe v3)
         (coe d_'8804''45'refl_3520 (coe v1)) (coe v5))
-- Data.Rational.Properties.+-monoˡ-<
d_'43''45'mono'737''45''60'_4386 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'43''45'mono'737''45''60'_4386 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''60''45''8804'_4332 (coe v1) (coe v2) (coe v0)
      (coe v0) (coe v3) (coe d_'8804''45'refl_3520 (coe v0))
-- Data.Rational.Properties.+-monoʳ-<
d_'43''45'mono'691''45''60'_4392 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'43''45'mono'691''45''60'_4392 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''8804''45''60'_4350 (coe v0) (coe v0) (coe v1)
      (coe v2) (coe d_'8804''45'refl_3520 (coe v0)) (coe v3)
-- Data.Rational.Properties.pos+nonNeg⇒pos
d_pos'43'nonNeg'8658'pos_4406 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_pos'43'nonNeg'8658'pos_4406 v0 ~v1 v2 ~v3
  = du_pos'43'nonNeg'8658'pos_4406 v0 v2
du_pos'43'nonNeg'8658'pos_4406 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_pos'43'nonNeg'8658'pos_4406 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_positive_240
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))
      (coe
         d_'43''45'mono'45''60''45''8804'_4332
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v0)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
         (coe du_positive'8315''185'_3900 (coe v0))
         (coe du_nonNegative'8315''185'_3906 (coe v1)))
-- Data.Rational.Properties.nonNeg+pos⇒pos
d_nonNeg'43'pos'8658'pos_4420 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_nonNeg'43'pos'8658'pos_4420 v0 ~v1 v2 ~v3
  = du_nonNeg'43'pos'8658'pos_4420 v0 v2
du_nonNeg'43'pos'8658'pos_4420 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_nonNeg'43'pos'8658'pos_4420 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_positive_240
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))
      (coe
         d_'43''45'mono'45''8804''45''60'_4350
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v0)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
         (coe du_nonNegative'8315''185'_3906 (coe v0))
         (coe du_positive'8315''185'_3900 (coe v1)))
-- Data.Rational.Properties.pos+pos⇒pos
d_pos'43'pos'8658'pos_4434 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_pos'43'pos'8658'pos_4434 v0 ~v1 v2 ~v3
  = du_pos'43'pos'8658'pos_4434 v0 v2
du_pos'43'pos'8658'pos_4434 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_pos'43'pos'8658'pos_4434 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_positive_240
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))
      (coe
         d_'43''45'mono'45''60'_4372
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v0)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
         (coe du_positive'8315''185'_3900 (coe v0))
         (coe du_positive'8315''185'_3900 (coe v1)))
-- Data.Rational.Properties.neg+nonPos⇒neg
d_neg'43'nonPos'8658'neg_4448 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_neg'43'nonPos'8658'neg_4448 v0 ~v1 v2 ~v3
  = du_neg'43'nonPos'8658'neg_4448 v0 v2
du_neg'43'nonPos'8658'neg_4448 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_neg'43'nonPos'8658'neg_4448 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_negative_248
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))
      (coe
         d_'43''45'mono'45''60''45''8804'_4332 (coe v0)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
         (coe du_negative'8315''185'_3912 (coe v0))
         (coe du_nonPositive'8315''185'_3918 (coe v1)))
-- Data.Rational.Properties.nonPos+neg⇒neg
d_nonPos'43'neg'8658'neg_4462 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_nonPos'43'neg'8658'neg_4462 v0 ~v1 v2 ~v3
  = du_nonPos'43'neg'8658'neg_4462 v0 v2
du_nonPos'43'neg'8658'neg_4462 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_nonPos'43'neg'8658'neg_4462 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_negative_248
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))
      (coe
         d_'43''45'mono'45''8804''45''60'_4350 (coe v0)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
         (coe du_nonPositive'8315''185'_3918 (coe v0))
         (coe du_negative'8315''185'_3912 (coe v1)))
-- Data.Rational.Properties.neg+neg⇒neg
d_neg'43'neg'8658'neg_4476 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_neg'43'neg'8658'neg_4476 v0 ~v1 v2 ~v3
  = du_neg'43'neg'8658'neg_4476 v0 v2
du_neg'43'neg'8658'neg_4476 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_neg'43'neg'8658'neg_4476 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_negative_248
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))
      (coe
         d_'43''45'mono'45''60'_4372 (coe v0)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
         (coe du_negative'8315''185'_3912 (coe v0))
         (coe du_negative'8315''185'_3912 (coe v1)))
-- Data.Rational.Properties.*-nf
d_'42''45'nf_4482 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 -> Integer
d_'42''45'nf_4482 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.GCD.d_gcd_136
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v0))
         (coe MAlonzo.Code.Data.Rational.Base.d_numerator_14 (coe v1)))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v0))
         (coe MAlonzo.Code.Data.Rational.Base.d_denominator_22 (coe v1)))
-- Data.Rational.Properties.↥-*
d_'8613''45''42'_4492 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''45''42'_4492 = erased
-- Data.Rational.Properties.↧-*
d_'8615''45''42'_4502 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''45''42'_4502 = erased
-- Data.Rational.Properties.toℚᵘ-homo-*
d_toℚ'7512''45'homo'45''42'_4508 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_toℚ'7512''45'homo'45''42'_4508 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6
               -> let v8
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased erased
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710
                               (coe
                                  MAlonzo.Code.Data.Nat.GCD.d_gcd_152
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                     (coe
                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2)
                                        (coe v5)))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                     (coe
                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe
                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                           (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3))
                                        (coe
                                           MAlonzo.Code.Data.Rational.Base.d_denominator_22
                                           (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6)))))
                               (coe (0 :: Integer))) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> coe
                              seq (coe v9)
                              (coe
                                 seq (coe v10)
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties._.eq2
d_eq2_4528 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq2_4528 = erased
-- Data.Rational.Properties._.eq
d_eq_4530 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_4530 = erased
-- Data.Rational.Properties.toℚᵘ-homo-1/
d_toℚ'7512''45'homo'45'1'47'_4666 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_toℚ'7512''45'homo'45'1'47'_4666 v0 ~v1
  = du_toℚ'7512''45'homo'45'1'47'_4666 v0
du_toℚ'7512''45'homo'45'1'47'_4666 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_toℚ'7512''45'homo'45'1'47'_4666 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'refl_166)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.toℚᵘ-isMagmaHomomorphism-*
d_toℚ'7512''45'isMagmaHomomorphism'45''42'_4668 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_188
d_toℚ'7512''45'isMagmaHomomorphism'45''42'_4668
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMagmaHomomorphism'46'constructor_4629
      (coe d_toℚ'7512''45'isRelHomomorphism_3444)
      (coe d_toℚ'7512''45'homo'45''42'_4508)
-- Data.Rational.Properties.toℚᵘ-isMonoidHomomorphism-*
d_toℚ'7512''45'isMonoidHomomorphism'45''42'_4670 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_362
d_toℚ'7512''45'isMonoidHomomorphism'45''42'_4670
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidHomomorphism'46'constructor_9411
      (coe d_toℚ'7512''45'isMagmaHomomorphism'45''42'_4668)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'refl_166)
-- Data.Rational.Properties.toℚᵘ-isMonoidMonomorphism-*
d_toℚ'7512''45'isMonoidMonomorphism'45''42'_4672 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384
d_toℚ'7512''45'isMonoidMonomorphism'45''42'_4672
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidMonomorphism'46'constructor_10237
      (coe d_toℚ'7512''45'isMonoidHomomorphism'45''42'_4670) erased
-- Data.Rational.Properties.toℚᵘ-isNearSemiringHomomorphism-+-*
d_toℚ'7512''45'isNearSemiringHomomorphism'45''43''45''42'_4674 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsNearSemiringHomomorphism_928
d_toℚ'7512''45'isNearSemiringHomomorphism'45''43''45''42'_4674
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsNearSemiringHomomorphism'46'constructor_19989
      (coe d_toℚ'7512''45'isMonoidHomomorphism'45''43'_4160)
      (coe d_toℚ'7512''45'homo'45''42'_4508)
-- Data.Rational.Properties.toℚᵘ-isNearSemiringMonomorphism-+-*
d_toℚ'7512''45'isNearSemiringMonomorphism'45''43''45''42'_4676 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsNearSemiringMonomorphism_956
d_toℚ'7512''45'isNearSemiringMonomorphism'45''43''45''42'_4676
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsNearSemiringMonomorphism'46'constructor_21119
      (coe
         d_toℚ'7512''45'isNearSemiringHomomorphism'45''43''45''42'_4674)
      erased
-- Data.Rational.Properties.toℚᵘ-isSemiringHomomorphism-+-*
d_toℚ'7512''45'isSemiringHomomorphism'45''43''45''42'_4678 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsSemiringHomomorphism_1294
d_toℚ'7512''45'isSemiringHomomorphism'45''43''45''42'_4678
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsSemiringHomomorphism'46'constructor_26561
      (coe
         d_toℚ'7512''45'isNearSemiringHomomorphism'45''43''45''42'_4674)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'refl_166)
-- Data.Rational.Properties.toℚᵘ-isSemiringMonomorphism-+-*
d_toℚ'7512''45'isSemiringMonomorphism'45''43''45''42'_4680 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsSemiringMonomorphism_1328
d_toℚ'7512''45'isSemiringMonomorphism'45''43''45''42'_4680
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsSemiringMonomorphism'46'constructor_27871
      (coe d_toℚ'7512''45'isSemiringHomomorphism'45''43''45''42'_4678)
      erased
-- Data.Rational.Properties.toℚᵘ-isRingHomomorphism-+-*
d_toℚ'7512''45'isRingHomomorphism'45''43''45''42'_4682 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingHomomorphism_2374
d_toℚ'7512''45'isRingHomomorphism'45''43''45''42'_4682
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsRingHomomorphism'46'constructor_43635
      (coe d_toℚ'7512''45'isSemiringHomomorphism'45''43''45''42'_4678)
      (coe d_toℚ'7512''45'homo'8255''45'_4164)
-- Data.Rational.Properties.toℚᵘ-isRingMonomorphism-+-*
d_toℚ'7512''45'isRingMonomorphism'45''43''45''42'_4684 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416
d_toℚ'7512''45'isRingMonomorphism'45''43''45''42'_4684
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsRingMonomorphism'46'constructor_45289
      (coe d_toℚ'7512''45'isRingHomomorphism'45''43''45''42'_4682) erased
-- Data.Rational.Properties.*-assoc
d_'42''45'assoc_4802 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_4802 = erased
-- Data.Rational.Properties.*-comm
d_'42''45'comm_4804 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_4804 = erased
-- Data.Rational.Properties.*-identityˡ
d_'42''45'identity'737'_4806 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_4806 = erased
-- Data.Rational.Properties.*-identityʳ
d_'42''45'identity'691'_4808 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_4808 = erased
-- Data.Rational.Properties.*-identity
d_'42''45'identity_4810 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_4810
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Rational.Properties.*-zeroˡ
d_'42''45'zero'737'_4812 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'737'_4812 = erased
-- Data.Rational.Properties.*-zeroʳ
d_'42''45'zero'691'_4814 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'691'_4814 = erased
-- Data.Rational.Properties.*-zero
d_'42''45'zero_4816 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'zero_4816
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Rational.Properties.*-distribˡ-+
d_'42''45'distrib'737''45''43'_4818 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''43'_4818 = erased
-- Data.Rational.Properties.*-distribʳ-+
d_'42''45'distrib'691''45''43'_4820 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''43'_4820 = erased
-- Data.Rational.Properties.*-distrib-+
d_'42''45'distrib'45''43'_4822 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''43'_4822
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Rational.Properties.*-inverseˡ
d_'42''45'inverse'737'_4828 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'inverse'737'_4828 = erased
-- Data.Rational.Properties.*-inverseʳ
d_'42''45'inverse'691'_4840 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'inverse'691'_4840 = erased
-- Data.Rational.Properties.neg-distribˡ-*
d_neg'45'distrib'737''45''42'_4848 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'737''45''42'_4848 = erased
-- Data.Rational.Properties.neg-distribʳ-*
d_neg'45'distrib'691''45''42'_4854 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'691''45''42'_4854 = erased
-- Data.Rational.Properties.*-isMagma
d_'42''45'isMagma_4856 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_4856
  = let v0
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                 (coe
                    MAlonzo.Code.Data.Rational.Base.d_'43''45''42''45'rawRing_376)) in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45''42''45'rawRing_296)) in
       coe
         (let v2 = MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 in
          coe
            (let v3
                   = coe
                       MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                       (coe d_toℚ'7512''45'isRingMonomorphism'45''43''45''42'_4684) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isMagma_238
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
                  (coe v2)
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                     (coe v3))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'42''45'isMagma_2456)))))
-- Data.Rational.Properties.*-isSemigroup
d_'42''45'isSemigroup_4858 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_4858
  = let v0
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                 (coe
                    MAlonzo.Code.Data.Rational.Base.d_'43''45''42''45'rawRing_376)) in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45''42''45'rawRing_296)) in
       coe
         (let v2 = MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 in
          coe
            (let v3
                   = coe
                       MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                       (coe d_toℚ'7512''45'isRingMonomorphism'45''43''45''42'_4684) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSemigroup_268
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
                  (coe v2)
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                     (coe v3))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'42''45'isSemigroup_2458)))))
-- Data.Rational.Properties.*-1-isMonoid
d_'42''45'1'45'isMonoid_4860 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'1'45'isMonoid_4860
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isMonoid_192
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
            (coe
               MAlonzo.Code.Data.Rational.Base.d_'43''45''42''45'rawRing_376)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45''42''45'rawRing_296)))
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe d_toℚ'7512''45'isRingMonomorphism'45''43''45''42'_4684))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'42''45'1'45'isMonoid_2460)
-- Data.Rational.Properties.*-1-isCommutativeMonoid
d_'42''45'1'45'isCommutativeMonoid_4862 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'1'45'isCommutativeMonoid_4862
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isCommutativeMonoid_236
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
            (coe
               MAlonzo.Code.Data.Rational.Base.d_'43''45''42''45'rawRing_376)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45''42''45'rawRing_296)))
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe d_toℚ'7512''45'isRingMonomorphism'45''43''45''42'_4684))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'42''45'1'45'isCommutativeMonoid_2462)
-- Data.Rational.Properties.+-*-isRing
d_'43''45''42''45'isRing_4864 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_'43''45''42''45'isRing_4864
  = coe
      MAlonzo.Code.Algebra.Morphism.RingMonomorphism.du_isRing_424
      (coe MAlonzo.Code.Data.Rational.Base.d_'43''45''42''45'rawRing_376)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45''42''45'rawRing_296)
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe d_toℚ'7512''45'isRingMonomorphism'45''43''45''42'_4684)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45''42''45'isRing_2464)
-- Data.Rational.Properties.+-*-isCommutativeRing
d_'43''45''42''45'isCommutativeRing_4866 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
d_'43''45''42''45'isCommutativeRing_4866
  = coe
      MAlonzo.Code.Algebra.Morphism.RingMonomorphism.du_isCommutativeRing_542
      (coe MAlonzo.Code.Data.Rational.Base.d_'43''45''42''45'rawRing_376)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'43''45''42''45'rawRing_296)
      (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166)
      (coe d_toℚ'7512''45'isRingMonomorphism'45''43''45''42'_4684)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45''42''45'isCommutativeRing_2466)
-- Data.Rational.Properties.*-magma
d_'42''45'magma_4868 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'42''45'magma_4868
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1323
      MAlonzo.Code.Data.Rational.Base.d__'42'__276 d_'42''45'isMagma_4856
-- Data.Rational.Properties.*-semigroup
d_'42''45'semigroup_4870 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'42''45'semigroup_4870
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9837
      MAlonzo.Code.Data.Rational.Base.d__'42'__276
      d_'42''45'isSemigroup_4858
-- Data.Rational.Properties.*-1-monoid
d_'42''45'1'45'monoid_4872 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'42''45'1'45'monoid_4872
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16201
      MAlonzo.Code.Data.Rational.Base.d__'42'__276
      MAlonzo.Code.Data.Rational.Base.d_1ℚ_180
      d_'42''45'1'45'isMonoid_4860
-- Data.Rational.Properties.*-1-commutativeMonoid
d_'42''45'1'45'commutativeMonoid_4874 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'42''45'1'45'commutativeMonoid_4874
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      MAlonzo.Code.Data.Rational.Base.d__'42'__276
      MAlonzo.Code.Data.Rational.Base.d_1ℚ_180
      d_'42''45'1'45'isCommutativeMonoid_4862
-- Data.Rational.Properties.+-*-ring
d_'43''45''42''45'ring_4876 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838
d_'43''45''42''45'ring_4876
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Ring'46'constructor_69425
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      MAlonzo.Code.Data.Rational.Base.d__'42'__276
      MAlonzo.Code.Data.Rational.Base.d_'45'__112
      MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      MAlonzo.Code.Data.Rational.Base.d_1ℚ_180
      d_'43''45''42''45'isRing_4864
-- Data.Rational.Properties.+-*-commutativeRing
d_'43''45''42''45'commutativeRing_4878 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4054
d_'43''45''42''45'commutativeRing_4878
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeRing'46'constructor_73489
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      MAlonzo.Code.Data.Rational.Base.d__'42'__276
      MAlonzo.Code.Data.Rational.Base.d_'45'__112
      MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      MAlonzo.Code.Data.Rational.Base.d_1ℚ_180
      d_'43''45''42''45'isCommutativeRing_4866
-- Data.Rational.Properties._.#⇒invertible
d_'35''8658'invertible_4972 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'35''8658'invertible_4972 v0 v1 ~v2
  = du_'35''8658'invertible_4972 v0 v1
du_'35''8658'invertible_4972 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'35''8658'invertible_4972 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.Rational.Base.du_1'47'__292
         (coe
            MAlonzo.Code.Data.Rational.Base.d__'45'__282 (coe v0) (coe v1)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Data.Rational.Properties._.invertible⇒#
d_invertible'8658''35'_4988 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_invertible'8658''35'_4988 = erased
-- Data.Rational.Properties._._.1≡0
d_1'8801'0_5044 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'8801'0_5044 = erased
-- Data.Rational.Properties._.isHeytingCommutativeRing
d_isHeytingCommutativeRing_5046 ::
  MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingCommutativeRing_160
d_isHeytingCommutativeRing_5046
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.C_IsHeytingCommutativeRing'46'constructor_4849
      (coe d_'43''45''42''45'isCommutativeRing_4866)
      (coe
         MAlonzo.Code.Relation.Binary.Properties.DecSetoid.du_'8777''45'isApartnessRelation_106
         (coe d_'8801''45'decSetoid_2718))
      (\ v0 v1 v2 -> coe du_'35''8658'invertible_4972 v0 v1) erased
-- Data.Rational.Properties._.isHeytingField
d_isHeytingField_5048 ::
  MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingField_464
d_isHeytingField_5048
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.C_IsHeytingField'46'constructor_16575
      (coe d_isHeytingCommutativeRing_5046)
      (coe
         MAlonzo.Code.Relation.Binary.Properties.DecSetoid.du_'8777''45'tight_110
         (coe d_'8801''45'decSetoid_2718))
-- Data.Rational.Properties._.heytingCommutativeRing
d_heytingCommutativeRing_5050 ::
  MAlonzo.Code.Algebra.Apartness.Bundles.T_HeytingCommutativeRing_12
d_heytingCommutativeRing_5050
  = coe
      MAlonzo.Code.Algebra.Apartness.Bundles.C_HeytingCommutativeRing'46'constructor_657
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      MAlonzo.Code.Data.Rational.Base.d__'42'__276
      MAlonzo.Code.Data.Rational.Base.d_'45'__112
      MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      MAlonzo.Code.Data.Rational.Base.d_1ℚ_180
      d_isHeytingCommutativeRing_5046
-- Data.Rational.Properties._.heytingField
d_heytingField_5052 ::
  MAlonzo.Code.Algebra.Apartness.Bundles.T_HeytingField_208
d_heytingField_5052
  = coe
      MAlonzo.Code.Algebra.Apartness.Bundles.C_HeytingField'46'constructor_4995
      MAlonzo.Code.Data.Rational.Base.d__'43'__270
      MAlonzo.Code.Data.Rational.Base.d__'42'__276
      MAlonzo.Code.Data.Rational.Base.d_'45'__112
      MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
      MAlonzo.Code.Data.Rational.Base.d_1ℚ_180 d_isHeytingField_5048
-- Data.Rational.Properties.*-cancelʳ-≤-pos
d_'42''45'cancel'691''45''8804''45'pos_5058 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'cancel'691''45''8804''45'pos_5058 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'691''45''8804''45'pos_5058 v0 v1 v2 v4
du_'42''45'cancel'691''45''8804''45'pos_5058 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'cancel'691''45''8804''45'pos_5058 v0 v1 v2 v3
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'42''45'cancel'691''45''8804''45'pos_2036
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
               (\ v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'60''8658''8804'_556
                    v6))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
               (\ v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                    v6)
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45''60''45'trans_610))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v2)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v2)))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))))
                     (d_toℚ'7512''45'homo'45''42'_4508 (coe v1) (coe v2)))
                  (d_toℚ'7512''45'mono'45''8804'_3452
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2))
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v2))
                     (coe v3)))
               (d_toℚ'7512''45'homo'45''42'_4508 (coe v0) (coe v2)))))
-- Data.Rational.Properties.*-cancelˡ-≤-pos
d_'42''45'cancel'737''45''8804''45'pos_5076 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'cancel'737''45''8804''45'pos_5076 v0 v1 v2 ~v3
  = du_'42''45'cancel'737''45''8804''45'pos_5076 v0 v1 v2
du_'42''45'cancel'737''45''8804''45'pos_5076 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'cancel'737''45''8804''45'pos_5076 v0 v1 v2
  = coe
      du_'42''45'cancel'691''45''8804''45'pos_5058 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Properties.*-monoʳ-≤-nonNeg
d_'42''45'mono'691''45''8804''45'nonNeg_5098 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'mono'691''45''8804''45'nonNeg_5098 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'691''45''8804''45'nonNeg_5098 v0 v2 v3 v4
du_'42''45'mono'691''45''8804''45'nonNeg_5098 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'mono'691''45''8804''45'nonNeg_5098 v0 v1 v2 v3
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
         (\ v4 v5 -> v4) v1 v2)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5)
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
         v1 v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'60''8658''8804'_556
                 v6))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (\ v4 ->
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
               (\ v4 v5 -> v4) v1 v2))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5)
               (\ v4 ->
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
               v1 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
            (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                  (\ v4 v5 -> v5)
                  (\ v4 ->
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
                  v1 v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45''60''45'trans_610))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5)
                     (\ v4 ->
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
                     v1 v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                  (\ v4 v5 v6 ->
                     coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                       v6)
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v4 v5 -> v5)
                        (\ v4 ->
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
                        v1 v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0))))
                  (d_toℚ'7512''45'homo'45''42'_4508 (coe v2) (coe v0)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'42''45'mono'737''45''8804''45'nonNeg_2114
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                  (coe
                     d_toℚ'7512''45'mono'45''8804'_3452 (coe v1) (coe v2) (coe v3))))
            (d_toℚ'7512''45'homo'45''42'_4508 (coe v1) (coe v0))))
-- Data.Rational.Properties.*-monoˡ-≤-nonNeg
d_'42''45'mono'737''45''8804''45'nonNeg_5118 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'mono'737''45''8804''45'nonNeg_5118 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804''45'nonNeg_5118 v0 v2 v3
du_'42''45'mono'737''45''8804''45'nonNeg_5118 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'mono'737''45''8804''45'nonNeg_5118 v0 v1 v2
  = coe
      du_'42''45'mono'691''45''8804''45'nonNeg_5098 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Properties.*-monoʳ-≤-nonPos
d_'42''45'mono'691''45''8804''45'nonPos_5140 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'mono'691''45''8804''45'nonPos_5140 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'691''45''8804''45'nonPos_5140 v0 v2 v3 v4
du_'42''45'mono'691''45''8804''45'nonPos_5140 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'mono'691''45''8804''45'nonPos_5140 v0 v1 v2 v3
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5)
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
         v1 v2)
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
         (\ v4 v5 -> v4) v1 v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'60''8658''8804'_556
                 v6))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v4 v5 -> v5)
               (\ v4 ->
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
               v1 v2))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (\ v4 ->
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
               (\ v4 v5 -> v4) v1 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
            (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (\ v4 ->
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
                  (\ v4 v5 -> v4) v1 v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45''60''45'trans_610))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (\ v4 ->
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
                     (\ v4 v5 -> v4) v1 v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                  (\ v4 v5 v6 ->
                     coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                       v6)
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (\ v4 ->
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
                        (\ v4 v5 -> v4) v1 v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0))))
                  (d_toℚ'7512''45'homo'45''42'_4508 (coe v1) (coe v0)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'42''45'mono'737''45''8804''45'nonPos_2196
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                  (coe
                     d_toℚ'7512''45'mono'45''8804'_3452 (coe v1) (coe v2) (coe v3))))
            (d_toℚ'7512''45'homo'45''42'_4508 (coe v2) (coe v0))))
-- Data.Rational.Properties.*-monoˡ-≤-nonPos
d_'42''45'mono'737''45''8804''45'nonPos_5160 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'mono'737''45''8804''45'nonPos_5160 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804''45'nonPos_5160 v0 v2 v3
du_'42''45'mono'737''45''8804''45'nonPos_5160 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'mono'737''45''8804''45'nonPos_5160 v0 v1 v2
  = coe
      du_'42''45'mono'691''45''8804''45'nonPos_5140 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Properties.*-cancelʳ-≤-neg
d_'42''45'cancel'691''45''8804''45'neg_5180 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'cancel'691''45''8804''45'neg_5180 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'691''45''8804''45'neg_5180 v0 v1 v2 v4
du_'42''45'cancel'691''45''8804''45'neg_5180 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'cancel'691''45''8804''45'neg_5180 v0 v1 v2 v3
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460 (coe v1) (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'42''45'cancel'691''45''8804''45'neg_2074
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
               (\ v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'60''8658''8804'_556
                    v6))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
               (\ v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                    v6)
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45''60''45'trans_610))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v2)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v2)))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))))
                     (d_toℚ'7512''45'homo'45''42'_4508 (coe v1) (coe v2)))
                  (d_toℚ'7512''45'mono'45''8804'_3452
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2))
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v2))
                     (coe v3)))
               (d_toℚ'7512''45'homo'45''42'_4508 (coe v0) (coe v2)))))
-- Data.Rational.Properties.*-cancelˡ-≤-neg
d_'42''45'cancel'737''45''8804''45'neg_5198 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'cancel'737''45''8804''45'neg_5198 v0 v1 v2 ~v3
  = du_'42''45'cancel'737''45''8804''45'neg_5198 v0 v1 v2
du_'42''45'cancel'737''45''8804''45'neg_5198 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'cancel'737''45''8804''45'neg_5198 v0 v1 v2
  = coe
      du_'42''45'cancel'691''45''8804''45'neg_5180 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Properties.nonNeg*nonNeg⇒nonNeg
d_nonNeg'42'nonNeg'8658'nonNeg_5222 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_nonNeg'42'nonNeg'8658'nonNeg_5222 v0 ~v1 v2 ~v3
  = du_nonNeg'42'nonNeg'8658'nonNeg_5222 v0 v2
du_nonNeg'42'nonNeg'8658'nonNeg_5222 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_nonNeg'42'nonNeg'8658'nonNeg_5222 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_nonNegative_264
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe d_'8804''45'isPreorder_3550)
            (\ v2 v3 v4 -> coe du_'60''8658''8804'_3588 v4))
         MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
         (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
            (\ v2 v3 v4 v5 v6 -> v6) MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
            (MAlonzo.Code.Data.Rational.Base.d__'42'__276
               (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
            (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe d_'8804''45'isPreorder_3550)
                  (coe d_'8804''45''60''45'trans_3680))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                  (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3550))
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1)))
               (coe
                  du_'42''45'mono'737''45''8804''45'nonNeg_5118 v0
                  MAlonzo.Code.Data.Rational.Base.d_0ℚ_178 v1
                  (coe du_nonNegative'8315''185'_3906 (coe v1))))
            erased))
-- Data.Rational.Properties.nonPos*nonNeg⇒nonPos
d_nonPos'42'nonNeg'8658'nonPos_5240 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
d_nonPos'42'nonNeg'8658'nonPos_5240 v0 ~v1 v2 ~v3
  = du_nonPos'42'nonNeg'8658'nonPos_5240 v0 v2
du_nonPos'42'nonNeg'8658'nonPos_5240 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
du_nonPos'42'nonNeg'8658'nonPos_5240 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_nonPositive_256
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe d_'8804''45'isPreorder_3550)
            (\ v2 v3 v4 -> coe du_'60''8658''8804'_3588 v4))
         (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
         MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_3550)
               (coe d_'8804''45''60''45'trans_3680))
            (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
            (MAlonzo.Code.Data.Rational.Base.d__'42'__276
               (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
            MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                  (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3550))
                  (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               erased)
            (coe
               du_'42''45'mono'737''45''8804''45'nonPos_5160 v0
               MAlonzo.Code.Data.Rational.Base.d_0ℚ_178 v1
               (coe du_nonNegative'8315''185'_3906 (coe v1)))))
-- Data.Rational.Properties.nonNeg*nonPos⇒nonPos
d_nonNeg'42'nonPos'8658'nonPos_5258 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
d_nonNeg'42'nonPos'8658'nonPos_5258 v0 ~v1 v2 ~v3
  = du_nonNeg'42'nonPos'8658'nonPos_5258 v0 v2
du_nonNeg'42'nonPos'8658'nonPos_5258 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
du_nonNeg'42'nonPos'8658'nonPos_5258 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_nonPositive_256
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe d_'8804''45'isPreorder_3550)
            (\ v2 v3 v4 -> coe du_'60''8658''8804'_3588 v4))
         (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
         MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_3550)
               (coe d_'8804''45''60''45'trans_3680))
            (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
            (MAlonzo.Code.Data.Rational.Base.d__'42'__276
               (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
            MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                  (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3550))
                  (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               erased)
            (coe
               du_'42''45'mono'737''45''8804''45'nonNeg_5118 v0 v1
               MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               (coe du_nonPositive'8315''185'_3918 (coe v1)))))
-- Data.Rational.Properties.nonPos*nonPos⇒nonPos
d_nonPos'42'nonPos'8658'nonPos_5276 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_nonPos'42'nonPos'8658'nonPos_5276 v0 ~v1 v2 ~v3
  = du_nonPos'42'nonPos'8658'nonPos_5276 v0 v2
du_nonPos'42'nonPos'8658'nonPos_5276 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_nonPos'42'nonPos'8658'nonPos_5276 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_nonNegative_264
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe d_'8804''45'isPreorder_3550)
            (\ v2 v3 v4 -> coe du_'60''8658''8804'_3588 v4))
         MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
         (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
            (\ v2 v3 v4 v5 v6 -> v6) MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
            (MAlonzo.Code.Data.Rational.Base.d__'42'__276
               (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
            (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe d_'8804''45'isPreorder_3550)
                  (coe d_'8804''45''60''45'trans_3680))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                  (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3550))
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1)))
               (coe
                  du_'42''45'mono'737''45''8804''45'nonPos_5160 v0 v1
                  MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
                  (coe du_nonPositive'8315''185'_3918 (coe v1))))
            erased))
-- Data.Rational.Properties.*-monoˡ-<-pos
d_'42''45'mono'737''45''60''45'pos_5292 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'mono'737''45''60''45'pos_5292 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60''45'pos_5292 v0 v2 v3 v4
du_'42''45'mono'737''45''60''45'pos_5292 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'mono'737''45''60''45'pos_5292 v0 v1 v2 v3
  = coe
      d_toℚ'7512''45'cancel'45''60'_3576
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
         (\ v4 v5 -> v4) v1 v2)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5)
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
         v1 v2)
      (let v4
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
            (coe
               MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'trans_678)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45''8804''45'trans_644))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                     (\ v5 v6 v7 ->
                        coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                          v7)
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0))))
                     (d_toℚ'7512''45'homo'45''42'_4508 (coe v2) (coe v0)))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'42''45'mono'737''45''60''45'pos_2240
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                     (coe d_toℚ'7512''45'mono'45''60'_3568 (coe v1) (coe v2) (coe v3))))
               (d_toℚ'7512''45'homo'45''42'_4508 (coe v1) (coe v0)))))
-- Data.Rational.Properties.*-monoʳ-<-pos
d_'42''45'mono'691''45''60''45'pos_5312 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'mono'691''45''60''45'pos_5312 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''60''45'pos_5312 v0 v2 v3
du_'42''45'mono'691''45''60''45'pos_5312 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'mono'691''45''60''45'pos_5312 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''60''45'pos_5292 (coe v0) (coe v1) (coe v2)
-- Data.Rational.Properties.*-cancelˡ-<-nonNeg
d_'42''45'cancel'737''45''60''45'nonNeg_5336 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'cancel'737''45''60''45'nonNeg_5336 v0 ~v1 v2 v3 v4
  = du_'42''45'cancel'737''45''60''45'nonNeg_5336 v0 v2 v3 v4
du_'42''45'cancel'737''45''60''45'nonNeg_5336 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'cancel'737''45''60''45'nonNeg_5336 v0 v1 v2 v3
  = coe
      d_toℚ'7512''45'cancel'45''60'_3576 (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'42''45'cancel'737''45''60''45'nonNeg_2328
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
         (let v4
                = coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
               (coe v4)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                  (\ v5 v6 v7 ->
                     coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                       v7)
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'trans_678)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45''8804''45'trans_644))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2)))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                        (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2)))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                              (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                              (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))))
                        (d_toℚ'7512''45'homo'45''42'_4508 (coe v0) (coe v2)))
                     (d_toℚ'7512''45'mono'45''60'_3568
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v2))
                        (coe v3)))
                  (d_toℚ'7512''45'homo'45''42'_4508 (coe v0) (coe v1))))))
-- Data.Rational.Properties.*-cancelʳ-<-nonNeg
d_'42''45'cancel'691''45''60''45'nonNeg_5358 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'cancel'691''45''60''45'nonNeg_5358 v0 ~v1 v2 v3
  = du_'42''45'cancel'691''45''60''45'nonNeg_5358 v0 v2 v3
du_'42''45'cancel'691''45''60''45'nonNeg_5358 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'cancel'691''45''60''45'nonNeg_5358 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonNeg_5336 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Properties.*-monoˡ-<-neg
d_'42''45'mono'737''45''60''45'neg_5380 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'mono'737''45''60''45'neg_5380 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60''45'neg_5380 v0 v2 v3 v4
du_'42''45'mono'737''45''60''45'neg_5380 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'mono'737''45''60''45'neg_5380 v0 v1 v2 v3
  = coe
      d_toℚ'7512''45'cancel'45''60'_3576
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5)
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
         v1 v2)
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v4) (coe v0))
         (\ v4 v5 -> v4) v1 v2)
      (let v4
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
            (coe
               MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'trans_678)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45''8804''45'trans_644))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                     (\ v5 v6 v7 ->
                        coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                          v7)
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1) (coe v0))))
                     (d_toℚ'7512''45'homo'45''42'_4508 (coe v1) (coe v0)))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'42''45'mono'737''45''60''45'neg_2350
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                     (coe d_toℚ'7512''45'mono'45''60'_3568 (coe v1) (coe v2) (coe v3))))
               (d_toℚ'7512''45'homo'45''42'_4508 (coe v2) (coe v0)))))
-- Data.Rational.Properties.*-monoʳ-<-neg
d_'42''45'mono'691''45''60''45'neg_5400 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'mono'691''45''60''45'neg_5400 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''60''45'neg_5400 v0 v2 v3
du_'42''45'mono'691''45''60''45'neg_5400 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'mono'691''45''60''45'neg_5400 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''60''45'neg_5380 (coe v0) (coe v1) (coe v2)
-- Data.Rational.Properties.*-cancelˡ-<-nonPos
d_'42''45'cancel'737''45''60''45'nonPos_5420 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'cancel'737''45''60''45'nonPos_5420 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''60''45'nonPos_5420 v0 v1 v2 v4
du_'42''45'cancel'737''45''60''45'nonPos_5420 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'cancel'737''45''60''45'nonPos_5420 v0 v1 v2 v3
  = coe
      d_toℚ'7512''45'cancel'45''60'_3576 (coe v1) (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'42''45'cancel'737''45''60''45'nonPos_2392
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
         (let v4
                = coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
               (coe v4)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                  (\ v5 v6 v7 ->
                     coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                       v7)
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'trans_678)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45''8804''45'trans_644))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v1)))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                        (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v1)))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                              (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v2))
                              (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))))
                        (d_toℚ'7512''45'homo'45''42'_4508 (coe v2) (coe v1)))
                     (d_toℚ'7512''45'mono'45''60'_3568
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v2) (coe v1))
                        (coe v3)))
                  (d_toℚ'7512''45'homo'45''42'_4508 (coe v2) (coe v0))))))
-- Data.Rational.Properties.*-cancelʳ-<-nonPos
d_'42''45'cancel'691''45''60''45'nonPos_5438 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'cancel'691''45''60''45'nonPos_5438 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''60''45'nonPos_5438 v0 v1 v2
du_'42''45'cancel'691''45''60''45'nonPos_5438 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'cancel'691''45''60''45'nonPos_5438 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonPos_5420 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Properties.pos*pos⇒pos
d_pos'42'pos'8658'pos_5462 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_pos'42'pos'8658'pos_5462 v0 ~v1 v2 ~v3
  = du_pos'42'pos'8658'pos_5462 v0 v2
du_pos'42'pos'8658'pos_5462 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_pos'42'pos'8658'pos_5462 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_positive_240
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v2) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
               (\ v3 v4 v5 v6 v7 -> v7) MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                  (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe d_'60''45'trans_3714)
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                     (coe d_'60''45''8804''45'trans_3646))
                  (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                     (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
                  (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
                  (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_3550))
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1)))
                  (coe
                     du_'42''45'mono'691''45''60''45'pos_5312 v0
                     MAlonzo.Code.Data.Rational.Base.d_0ℚ_178 v1
                     (coe du_positive'8315''185'_3900 (coe v1))))
               erased)))
-- Data.Rational.Properties.neg*pos⇒neg
d_neg'42'pos'8658'neg_5480 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_neg'42'pos'8658'neg_5480 v0 ~v1 v2 ~v3
  = du_neg'42'pos'8658'neg_5480 v0 v2
du_neg'42'pos'8658'neg_5480 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_neg'42'pos'8658'neg_5480 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_negative_248
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
            (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe d_'60''45'trans_3714)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (coe d_'60''45''8804''45'trans_3646))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                  (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                     (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
                  MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
                  MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_3550))
                     (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
                  erased)
               (coe
                  du_'42''45'mono'691''45''60''45'neg_5400 v0
                  MAlonzo.Code.Data.Rational.Base.d_0ℚ_178 v1
                  (coe du_positive'8315''185'_3900 (coe v1))))))
-- Data.Rational.Properties.pos*neg⇒neg
d_pos'42'neg'8658'neg_5498 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_pos'42'neg'8658'neg_5498 v0 ~v1 v2 ~v3
  = du_pos'42'neg'8658'neg_5498 v0 v2
du_pos'42'neg'8658'neg_5498 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_pos'42'neg'8658'neg_5498 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_negative_248
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
            (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe d_'60''45'trans_3714)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (coe d_'60''45''8804''45'trans_3646))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                  (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                     (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
                  MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
                  MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_3550))
                     (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
                  erased)
               (coe
                  du_'42''45'mono'691''45''60''45'pos_5312 v0 v1
                  MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
                  (coe du_negative'8315''185'_3912 (coe v1))))))
-- Data.Rational.Properties.neg*neg⇒pos
d_neg'42'neg'8658'pos_5516 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_neg'42'neg'8658'pos_5516 v0 ~v1 v2 ~v3
  = du_neg'42'neg'8658'pos_5516 v0 v2
du_neg'42'neg'8658'pos_5516 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_neg'42'neg'8658'pos_5516 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_positive_240
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v2) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
               (\ v3 v4 v5 v6 v7 -> v7) MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                  (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
               (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe d_'60''45'trans_3714)
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                     (coe d_'60''45''8804''45'trans_3646))
                  (MAlonzo.Code.Data.Rational.Base.d__'42'__276
                     (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
                  (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
                  (MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_3550))
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v0) (coe v1)))
                  (coe
                     du_'42''45'mono'691''45''60''45'neg_5400 v0 v1
                     MAlonzo.Code.Data.Rational.Base.d_0ℚ_178
                     (coe du_negative'8315''185'_3912 (coe v1))))
               erased)))
-- Data.Rational.Properties.p≤q⇒p⊔q≡q
d_p'8804'q'8658'p'8852'q'8801'q_5526 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'8804'q'8658'p'8852'q'8801'q_5526 = erased
-- Data.Rational.Properties.p≥q⇒p⊔q≡p
d_p'8805'q'8658'p'8852'q'8801'p_5552 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'8805'q'8658'p'8852'q'8801'p_5552 = erased
-- Data.Rational.Properties.p≤q⇒p⊓q≡p
d_p'8804'q'8658'p'8851'q'8801'p_5578 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'8804'q'8658'p'8851'q'8801'p_5578 = erased
-- Data.Rational.Properties.p≥q⇒p⊓q≡q
d_p'8805'q'8658'p'8851'q'8801'q_5604 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'8805'q'8658'p'8851'q'8801'q_5604 = erased
-- Data.Rational.Properties.⊓-operator
d_'8851''45'operator_5630 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106
d_'8851''45'operator_5630
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MinOperator'46'constructor_1157
      (coe MAlonzo.Code.Data.Rational.Base.d__'8851'__332) erased erased
-- Data.Rational.Properties.⊔-operator
d_'8852''45'operator_5632 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_136
d_'8852''45'operator_5632
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MaxOperator'46'constructor_1701
      (coe MAlonzo.Code.Data.Rational.Base.d__'8852'__322) erased erased
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_5644 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8804'x_5644
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2838
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_5646 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8804'y'8658'x'8851'z'8804'y_5646
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3190
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_5648 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8804'y'8658'z'8851'x'8804'y_5648
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3202
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_5650 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8804'y'8658'x'8851'z'8804'y_5650
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3190
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_5652 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8804'y'8658'z'8851'x'8804'y_5652
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3202
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_5654 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8804'y'8851'z'8658'x'8804'y_5654
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3214
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_5656 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8804'y'8851'z'8658'x'8804'z_5656
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3228
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_5658 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8804'y_5658
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2864
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_5660 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8776'x'8658'x'8804'y_5660
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3098
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_5662 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8776'y'8658'y'8804'x_5662
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3130
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_5664 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8804'x_5664
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2838
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≤x⊔y
d_x'8851'y'8804'x'8852'y_5666 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8804'x'8852'y_5666
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_x'8851'y'8804'x'8852'y_3354
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_5668 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8804'y_5668
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2864
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_5670 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8776'x'8658'x'8804'y_5670
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3098
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_5672 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8851'y'8776'y'8658'y'8804'x_5672
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3130
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_5674 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8804'y'8851'z'8658'x'8804'y_5674
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3214
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_5676 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_x'8804'y'8851'z'8658'x'8804'z_5676
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3228
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-absorbs-⊔
d_'8851''45'absorbs'45''8852'_5678 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'absorbs'45''8852'_5678 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_5680 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_5680 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_5682 :: MAlonzo.Code.Algebra.Bundles.T_Band_600
d_'8851''45'band_5682
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3082
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_5684 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_5684 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_5686 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_'8851''45'commutativeSemigroup_5686
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3084
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-distrib-⊔
d_'8851''45'distrib'45''8852'_5694 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'distrib'45''8852'_5694
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3174
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-properties.⊓-distribʳ-⊔
d_'8851''45'distrib'691''45''8852'_5696 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'691''45''8852'_5696 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-distribˡ-⊔
d_'8851''45'distrib'737''45''8852'_5698 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'737''45''8852'_5698 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_5700 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8851''45'glb_5700
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3308
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_5702 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_5702 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_5710 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_'8851''45'isBand_5710
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3064
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_5712 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'8851''45'isCommutativeSemigroup_5712
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3066
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_5714 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_5714
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3060
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_5718 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
d_'8851''45'isSelectiveMagma_5718
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3068
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_5720 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'8851''45'isSemigroup_5720
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3062
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_5722 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'8851''45'magma_5722
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3078
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_5724 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8851''45'mono'45''8804'_5724
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3236
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_5728 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8851''45'mono'691''45''8804'_5728
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3296
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_5730 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8851''45'mono'737''45''8804'_5730
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3286
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_5734 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_5734
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3018
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_5736 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_126
d_'8851''45'selectiveMagma_5736
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3086
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_5738 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'8851''45'semigroup_5738
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3080
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_5740 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_5740 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-⊔-absorptive
d_'8851''45''8852''45'absorptive_5748 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45''8852''45'absorptive_5748
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'absorptive_3254
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-properties.⊔-absorbs-⊓
d_'8852''45'absorbs'45''8851'_5750 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'absorbs'45''8851'_5750 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_5752 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_5752 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_5754 :: MAlonzo.Code.Algebra.Bundles.T_Band_600
d_'8851''45'band_5754
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3082
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_5756 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_5756 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_5758 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_'8851''45'commutativeSemigroup_5758
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3084
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊔-distrib-⊓
d_'8852''45'distrib'45''8851'_5766 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'distrib'45''8851'_5766
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'45''8851'_3206
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-properties.⊔-distribʳ-⊓
d_'8852''45'distrib'691''45''8851'_5768 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'691''45''8851'_5768 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊔-distribˡ-⊓
d_'8852''45'distrib'737''45''8851'_5770 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'737''45''8851'_5770 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_5772 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_5772 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_5780 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_'8851''45'isBand_5780
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3064
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_5782 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'8851''45'isCommutativeSemigroup_5782
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3066
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_5784 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_5784
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3060
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_5788 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
d_'8851''45'isSelectiveMagma_5788
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3068
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_5790 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'8851''45'isSemigroup_5790
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3062
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_5792 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8851''45'glb_5792
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3308
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_5794 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'8851''45'magma_5794
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3078
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_5796 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8851''45'mono'45''8804'_5796
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3236
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_5800 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8851''45'mono'691''45''8804'_5800
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3296
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_5802 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8851''45'mono'737''45''8804'_5802
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3286
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_5804 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_5804
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3018
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_5806 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_126
d_'8851''45'selectiveMagma_5806
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3086
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_5808 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'8851''45'semigroup_5808
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3080
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_5810 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_5810 = erased
-- Data.Rational.Properties.⊓-⊔-properties.⊔-⊓-absorptive
d_'8852''45''8851''45'absorptive_5818 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45''8851''45'absorptive_5818
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'absorptive_3252
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_5822 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588
d_'8851''45'isSemilattice_5822
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_610
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_5824 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_5824
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8851''45'operator_5630 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_612
            (coe v0) (coe v1)))
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊓-⊔-distributiveLattice
d_'8851''45''8852''45'distributiveLattice_5826 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8851''45''8852''45'distributiveLattice_5826
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'distributiveLattice_816
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊓-⊔-isDistributiveLattice
d_'8851''45''8852''45'isDistributiveLattice_5828 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_'8851''45''8852''45'isDistributiveLattice_5828
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isDistributiveLattice_806
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊓-⊔-isLattice
d_'8851''45''8852''45'isLattice_5830 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_'8851''45''8852''45'isLattice_5830
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isLattice_804
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊓-⊔-lattice
d_'8851''45''8852''45'lattice_5832 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8851''45''8852''45'lattice_5832
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'lattice_812
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_5834 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588
d_'8851''45'isSemilattice_5834
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_610
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_5836 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_5836
  = let v0 = d_'8804''45'totalPreorder_3560 in
    coe
      (let v1 = d_'8852''45'operator_5632 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_612
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊔-⊓-distributiveLattice
d_'8852''45''8851''45'distributiveLattice_5838 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8852''45''8851''45'distributiveLattice_5838
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'distributiveLattice_814
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊔-⊓-isDistributiveLattice
d_'8852''45''8851''45'isDistributiveLattice_5840 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_'8852''45''8851''45'isDistributiveLattice_5840
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isDistributiveLattice_808
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊔-⊓-isLattice
d_'8852''45''8851''45'isLattice_5842 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_'8852''45''8851''45'isLattice_5842
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isLattice_802
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.⊓-⊔-latticeProperties.⊔-⊓-lattice
d_'8852''45''8851''45'lattice_5844 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8852''45''8851''45'lattice_5844
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'lattice_810
      (coe d_'8804''45'totalPreorder_3560)
      (coe d_'8851''45'operator_5630) (coe d_'8852''45'operator_5632)
-- Data.Rational.Properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_5852 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54) ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8852'_5852 = erased
-- Data.Rational.Properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_5862 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54) ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8851'_5862 = erased
-- Data.Rational.Properties.mono-<-distrib-⊓
d_mono'45''60''45'distrib'45''8851'_5872 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
   MAlonzo.Code.Data.Rational.Base.T__'60'__62) ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''60''45'distrib'45''8851'_5872 = erased
-- Data.Rational.Properties.mono-<-distrib-⊔
d_mono'45''60''45'distrib'45''8852'_5944 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
   MAlonzo.Code.Data.Rational.Base.T__'60'__62) ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''60''45'distrib'45''8852'_5944 = erased
-- Data.Rational.Properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_6016 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54) ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8851'_6016 = erased
-- Data.Rational.Properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_6026 ::
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6) ->
  (MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
   MAlonzo.Code.Data.Rational.Base.T__'8804'__54) ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8852'_6026 = erased
-- Data.Rational.Properties.*-distribˡ-⊓-nonNeg
d_'42''45'distrib'737''45''8851''45'nonNeg_6038 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8851''45'nonNeg_6038 = erased
-- Data.Rational.Properties.*-distribʳ-⊓-nonNeg
d_'42''45'distrib'691''45''8851''45'nonNeg_6050 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8851''45'nonNeg_6050 = erased
-- Data.Rational.Properties.*-distribˡ-⊔-nonNeg
d_'42''45'distrib'737''45''8852''45'nonNeg_6062 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8852''45'nonNeg_6062 = erased
-- Data.Rational.Properties.*-distribʳ-⊔-nonNeg
d_'42''45'distrib'691''45''8852''45'nonNeg_6074 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8852''45'nonNeg_6074 = erased
-- Data.Rational.Properties.*-distribˡ-⊔-nonPos
d_'42''45'distrib'737''45''8852''45'nonPos_6086 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8852''45'nonPos_6086 = erased
-- Data.Rational.Properties.*-distribʳ-⊔-nonPos
d_'42''45'distrib'691''45''8852''45'nonPos_6098 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8852''45'nonPos_6098 = erased
-- Data.Rational.Properties.*-distribˡ-⊓-nonPos
d_'42''45'distrib'737''45''8851''45'nonPos_6110 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8851''45'nonPos_6110 = erased
-- Data.Rational.Properties.*-distribʳ-⊓-nonPos
d_'42''45'distrib'691''45''8851''45'nonPos_6122 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8851''45'nonPos_6122 = erased
-- Data.Rational.Properties.nonZero⇒1/nonZero
d_nonZero'8658'1'47'nonZero_6130 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_nonZero'8658'1'47'nonZero_6130 v0 ~v1
  = du_nonZero'8658'1'47'nonZero_6130 v0
du_nonZero'8658'1'47'nonZero_6130 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_nonZero'8658'1'47'nonZero_6130 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.1/-involutive
d_1'47''45'involutive_6136 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'47''45'involutive_6136 = erased
-- Data.Rational.Properties.1/pos⇒pos
d_1'47'pos'8658'pos_6150 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_1'47'pos'8658'pos_6150 v0 ~v1 = du_1'47'pos'8658'pos_6150 v0
du_1'47'pos'8658'pos_6150 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_1'47'pos'8658'pos_6150 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_Positive'46'constructor_1399
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Properties.1/neg⇒neg
d_1'47'neg'8658'neg_6156 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_1'47'neg'8658'neg_6156 v0 ~v1 = du_1'47'neg'8658'neg_6156 v0
du_1'47'neg'8658'neg_6156 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_1'47'neg'8658'neg_6156 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_Negative'46'constructor_1573
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Properties.pos⇒1/pos
d_pos'8658'1'47'pos_6164 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_pos'8658'1'47'pos_6164 v0 ~v1 ~v2 = du_pos'8658'1'47'pos_6164 v0
du_pos'8658'1'47'pos_6164 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_pos'8658'1'47'pos_6164 v0
  = coe
      du_1'47'pos'8658'pos_6150
      (coe MAlonzo.Code.Data.Rational.Base.du_1'47'__292 (coe v0))
-- Data.Rational.Properties.neg⇒1/neg
d_neg'8658'1'47'neg_6174 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_neg'8658'1'47'neg_6174 v0 ~v1 ~v2 = du_neg'8658'1'47'neg_6174 v0
du_neg'8658'1'47'neg_6174 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_neg'8658'1'47'neg_6174 v0
  = coe
      du_1'47'neg'8658'neg_6156
      (coe MAlonzo.Code.Data.Rational.Base.du_1'47'__292 (coe v0))
-- Data.Rational.Properties.toℚᵘ-homo-∣-∣
d_toℚ'7512''45'homo'45''8739''45''8739'_6178 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_toℚ'7512''45'homo'45''8739''45''8739'_6178 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.∣p∣≡0⇒p≡0
d_'8739'p'8739''8801'0'8658'p'8801'0_6182 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'p'8739''8801'0'8658'p'8801'0_6182 = erased
-- Data.Rational.Properties.0≤∣p∣
d_0'8804''8739'p'8739'_6188 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_0'8804''8739'p'8739'_6188 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2
        -> coe
             MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe
                      MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                   (\ v4 v5 v6 ->
                      coe
                        MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868 v6))
                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                   (coe
                      MAlonzo.Code.Data.Rational.Base.d_numerator_14
                      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
                   (coe
                      MAlonzo.Code.Data.Rational.Base.d_denominator_22
                      (coe
                         MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                         (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2))))
                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                   (coe
                      MAlonzo.Code.Data.Rational.Base.d_numerator_14
                      (coe
                         MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                         (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2)))
                   (coe
                      MAlonzo.Code.Data.Rational.Base.d_denominator_22
                      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                   (\ v4 v5 v6 v7 v8 -> v8)
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                      (coe
                         MAlonzo.Code.Data.Rational.Base.d_numerator_14
                         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178))
                      (coe
                         MAlonzo.Code.Data.Rational.Base.d_denominator_22
                         (coe
                            MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                            (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2))))
                   MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                      (coe
                         MAlonzo.Code.Data.Rational.Base.d_numerator_14
                         (coe
                            MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                            (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2)))
                      (coe
                         MAlonzo.Code.Data.Rational.Base.d_denominator_22
                         (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe
                            MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                         (\ v4 v5 v6 v7 v8 ->
                            coe
                              MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                              v7 v8))
                      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                      (MAlonzo.Code.Data.Rational.Base.d_numerator_14
                         (coe
                            MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                            (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2)))
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                         (coe
                            MAlonzo.Code.Data.Rational.Base.d_numerator_14
                            (coe
                               MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                               (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2)))
                         (coe
                            MAlonzo.Code.Data.Rational.Base.d_denominator_22
                            (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                         (\ v4 v5 v6 v7 v8 -> v8)
                         (MAlonzo.Code.Data.Rational.Base.d_numerator_14
                            (coe
                               MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                               (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2)))
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                            (coe
                               MAlonzo.Code.Data.Rational.Base.d_numerator_14
                               (coe
                                  MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                  (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2)))
                            (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                            (coe
                               MAlonzo.Code.Data.Rational.Base.d_numerator_14
                               (coe
                                  MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                  (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2)))
                            (coe
                               MAlonzo.Code.Data.Rational.Base.d_denominator_22
                               (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178)))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe
                                  MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                               (coe
                                  MAlonzo.Code.Data.Rational.Base.d_numerator_14
                                  (coe
                                     MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                     (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2)))
                               (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16)))
                         erased)
                      (coe
                         MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.0≤p⇒∣p∣≡p
d_0'8804'p'8658''8739'p'8739''8801'p_6196 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8804'p'8658''8739'p'8739''8801'p_6196 = erased
-- Data.Rational.Properties.∣-p∣≡∣p∣
d_'8739''45'p'8739''8801''8739'p'8739'_6204 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45'p'8739''8801''8739'p'8739'_6204 = erased
-- Data.Rational.Properties.∣p∣≡p⇒0≤p
d_'8739'p'8739''8801'p'8658'0'8804'p_6218 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8739'p'8739''8801'p'8658'0'8804'p_6218 v0 ~v1
  = du_'8739'p'8739''8801'p'8658'0'8804'p_6218 v0
du_'8739'p'8739''8801'p'8658'0'8804'p_6218 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'8739'p'8739''8801'p'8658'0'8804'p_6218 v0
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460
      (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8739'p'8739''8771'p'8658'0'8804'p_3314
         (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
         (let v1
                = coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
               (coe v1)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
               (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0)))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v2 v3 v4 v5 v6 -> v6)
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0)))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                     erased)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                     (coe d_toℚ'7512''45'homo'45''8739''45''8739'_6178 (coe v0)))))))
-- Data.Rational.Properties.∣p∣≡p∨∣p∣≡-p
d_'8739'p'8739''8801'p'8744''8739'p'8739''8801''45'p_6230 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8739'p'8739''8801'p'8744''8739'p'8739''8801''45'p_6230 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2
        -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.∣p+q∣≤∣p∣+∣q∣
d_'8739'p'43'q'8739''8804''8739'p'8739''43''8739'q'8739'_6244 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8739'p'43'q'8739''8804''8739'p'8739''43''8739'q'8739'_6244 v0 v1
  = coe
      d_toℚ'7512''45'cancel'45''8804'_3460
      (coe
         MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
         (coe
            MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'43'__270
         (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
         (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
            (\ v2 v3 v4 ->
               coe
                 MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'60''8658''8804'_556
                 v4))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
            (coe
               MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))))
         (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
            (coe
               MAlonzo.Code.Data.Rational.Base.d__'43'__270
               (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
               (coe
                  MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
               (coe
                  MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))))
            (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'43'__270
                  (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1))))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))))
               (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d__'43'__270
                     (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45''60''45'trans_610))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                        (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))))
                  (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'43'__270
                        (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                     (\ v2 v3 v4 ->
                        coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                          v4)
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0)))
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
                     (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d__'43'__270
                           (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512)
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'60''45'resp'45''8771'_780))
                        (\ v2 v3 v4 ->
                           coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Properties.du_'8771''45'sym_170
                             v4)
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                              (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0)))
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                              (coe
                                 MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
                        (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d__'43'__270
                              (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
                              (coe
                                 MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
                        (MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d__'43'__270
                              (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
                              (coe
                                 MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8804''45'isPreorder_512))
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                              (coe
                                 MAlonzo.Code.Data.Rational.Base.d__'43'__270
                                 (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
                                 (coe
                                    MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1)))))
                        (d_toℚ'7512''45'homo'45''43'_4004
                           (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0))
                           (coe
                              MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1))))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'43''45'cong_1006
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v0)))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0)))
                        (coe
                           MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                           (coe MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338 (coe v1)))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                           (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
                        (coe d_toℚ'7512''45'homo'45''8739''45''8739'_6178 (coe v0))
                        (coe d_toℚ'7512''45'homo'45''8739''45''8739'_6178 (coe v1))))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8739'p'43'q'8739''8804''8739'p'8739''43''8739'q'8739'_3344
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1))))
               (MAlonzo.Code.Data.Rational.Unnormalised.Properties.d_'8739''45''8739''45'cong_3210
                  (coe
                     MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166
                     (coe
                        MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Base.d_toℚ'7512'_166 (coe v1)))
                  (coe d_toℚ'7512''45'homo'45''43'_4004 (coe v0) (coe v1))))
            (d_toℚ'7512''45'homo'45''8739''45''8739'_6178
               (coe
                  MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v0) (coe v1)))))
-- Data.Rational.Properties.∣p-q∣≤∣p∣+∣q∣
d_'8739'p'45'q'8739''8804''8739'p'8739''43''8739'q'8739'_6258 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'8739'p'45'q'8739''8804''8739'p'8739''43''8739'q'8739'_6258 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                       (coe d_'8804''45'isPreorder_3550)
                       (\ v8 v9 v10 -> coe du_'60''8658''8804'_3588 v10))
                    (MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                       (coe
                          MAlonzo.Code.Data.Rational.Base.d__'45'__282
                          (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3)
                          (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6)))
                    (MAlonzo.Code.Data.Rational.Base.d__'43'__270
                       (coe
                          MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                          (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3))
                       (coe
                          MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                          (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6)))
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                          (coe d_'8804''45'isPreorder_3550)
                          (coe d_'8804''45''60''45'trans_3680))
                       (MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                          (coe
                             MAlonzo.Code.Data.Rational.Base.d__'45'__282
                             (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3)
                             (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6)))
                       (MAlonzo.Code.Data.Rational.Base.d__'43'__270
                          (coe
                             MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                             (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3))
                          (coe
                             MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                             (coe
                                MAlonzo.Code.Data.Rational.Base.d_'45'__112
                                (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6))))
                       (MAlonzo.Code.Data.Rational.Base.d__'43'__270
                          (coe
                             MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                             (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3))
                          (coe
                             MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                             (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6)))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                          (\ v8 v9 v10 v11 v12 -> v12)
                          (MAlonzo.Code.Data.Rational.Base.d__'43'__270
                             (coe
                                MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3))
                             (coe
                                MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                (coe
                                   MAlonzo.Code.Data.Rational.Base.d_'45'__112
                                   (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6))))
                          (MAlonzo.Code.Data.Rational.Base.d__'43'__270
                             (coe
                                MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3))
                             (coe
                                MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6)))
                          (MAlonzo.Code.Data.Rational.Base.d__'43'__270
                             (coe
                                MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3))
                             (coe
                                MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6)))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                (coe d_'8804''45'isPreorder_3550))
                             (coe
                                MAlonzo.Code.Data.Rational.Base.d__'43'__270
                                (coe
                                   MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                   (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3))
                                (coe
                                   MAlonzo.Code.Data.Rational.Base.d_'8739'_'8739'_338
                                   (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6))))
                          erased)
                       (d_'8739'p'43'q'8739''8804''8739'p'8739''43''8739'q'8739'_6244
                          (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v2 v3)
                          (coe
                             MAlonzo.Code.Data.Rational.Base.d_'45'__112
                             (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v5 v6))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.∣p*q∣≡∣p∣*∣q∣
d_'8739'p'42'q'8739''8801''8739'p'8739''42''8739'q'8739'_6274 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'p'42'q'8739''8801''8739'p'8739''42''8739'q'8739'_6274
  = erased
-- Data.Rational.Properties.∣-∣-nonNeg
d_'8739''45''8739''45'nonNeg_6286 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_'8739''45''8739''45'nonNeg_6286 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_NonNegative'46'constructor_1457
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.∣∣p∣∣≡∣p∣
d_'8739''8739'p'8739''8739''8801''8739'p'8739'_6290 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8739'p'8739''8739''8801''8739'p'8739'_6290 = erased
-- Data.Rational.Properties.*-monoʳ-≤-neg
d_'42''45'mono'691''45''8804''45'neg_6298 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'mono'691''45''8804''45'neg_6298 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804''45'neg_6298 v0 v2 v3
du_'42''45'mono'691''45''8804''45'neg_6298 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'mono'691''45''8804''45'neg_6298 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
                 coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    du_'42''45'mono'691''45''8804''45'nonPos_5140
                    (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4) (coe v1)
                    (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.*-monoˡ-≤-neg
d_'42''45'mono'737''45''8804''45'neg_6306 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'mono'737''45''8804''45'neg_6306 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804''45'neg_6306 v0 v2 v3
du_'42''45'mono'737''45''8804''45'neg_6306 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'mono'737''45''8804''45'neg_6306 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
                 coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    du_'42''45'mono'737''45''8804''45'nonPos_5160
                    (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4) (coe v1)
                    (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.*-monoʳ-≤-pos
d_'42''45'mono'691''45''8804''45'pos_6314 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'mono'691''45''8804''45'pos_6314 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804''45'pos_6314 v0 v2 v3
du_'42''45'mono'691''45''8804''45'pos_6314 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'mono'691''45''8804''45'pos_6314 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             0 -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   du_'42''45'mono'691''45''8804''45'nonNeg_5098
                   (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4) (coe v1)
                   (coe v2)
             _ -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.*-monoˡ-≤-pos
d_'42''45'mono'737''45''8804''45'pos_6322 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_'42''45'mono'737''45''8804''45'pos_6322 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804''45'pos_6322 v0 v2 v3
du_'42''45'mono'737''45''8804''45'pos_6322 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_'42''45'mono'737''45''8804''45'pos_6322 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             0 -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   du_'42''45'mono'737''45''8804''45'nonNeg_5118
                   (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4) (coe v1)
                   (coe v2)
             _ -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.*-cancelˡ-<-pos
d_'42''45'cancel'737''45''60''45'pos_6332 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'cancel'737''45''60''45'pos_6332 v0 ~v1 v2 v3
  = du_'42''45'cancel'737''45''60''45'pos_6332 v0 v2 v3
du_'42''45'cancel'737''45''60''45'pos_6332 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'cancel'737''45''60''45'pos_6332 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             0 -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   du_'42''45'cancel'737''45''60''45'nonNeg_5336
                   (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4) (coe v1)
                   (coe v2)
             _ -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.*-cancelʳ-<-pos
d_'42''45'cancel'691''45''60''45'pos_6342 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'cancel'691''45''60''45'pos_6342 v0 ~v1 v2 v3
  = du_'42''45'cancel'691''45''60''45'pos_6342 v0 v2 v3
du_'42''45'cancel'691''45''60''45'pos_6342 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'cancel'691''45''60''45'pos_6342 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             0 -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   du_'42''45'cancel'691''45''60''45'nonNeg_5358
                   (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4) (coe v1)
                   (coe v2)
             _ -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.*-cancelˡ-<-neg
d_'42''45'cancel'737''45''60''45'neg_6352 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'cancel'737''45''60''45'neg_6352 v0 ~v1 v2 v3
  = du_'42''45'cancel'737''45''60''45'neg_6352 v0 v2 v3
du_'42''45'cancel'737''45''60''45'neg_6352 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'cancel'737''45''60''45'neg_6352 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
                 coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    du_'42''45'cancel'737''45''60''45'nonPos_5420 (coe v1) (coe v2)
                    (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.*-cancelʳ-<-neg
d_'42''45'cancel'691''45''60''45'neg_6362 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_'42''45'cancel'691''45''60''45'neg_6362 v0 ~v1 v2 v3
  = du_'42''45'cancel'691''45''60''45'neg_6362 v0 v2 v3
du_'42''45'cancel'691''45''60''45'neg_6362 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_'42''45'cancel'691''45''60''45'neg_6362 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4
        -> case coe v3 of
             _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
                 coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    du_'42''45'cancel'691''45''60''45'nonPos_5438 (coe v1) (coe v2)
                    (coe MAlonzo.Code.Data.Rational.Base.C_mkℚ_24 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Properties.negative<positive
d_negative'60'positive_6366 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
d_negative'60'positive_6366 v0 v1 ~v2 ~v3
  = du_negative'60'positive_6366 v0 v1
du_negative'60'positive_6366 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'60'__62
du_negative'60'positive_6366 v0 v1
  = coe du_neg'60'pos_3926 (coe v0) (coe v1)
