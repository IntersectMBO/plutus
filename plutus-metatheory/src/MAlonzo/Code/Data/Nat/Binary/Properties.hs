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

module MAlonzo.Code.Data.Nat.Binary.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Properties.CommutativeSemigroup
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Binary.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Function.Consequences.Propositional
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Morphism.Structures
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Nat.Binary.Properties._._DistributesOver_
d__DistributesOver__12 ::
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d__DistributesOver__12 = erased
-- Data.Nat.Binary.Properties._._DistributesOverʳ_
d__DistributesOver'691'__14 ::
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d__DistributesOver'691'__14 = erased
-- Data.Nat.Binary.Properties._._DistributesOverˡ_
d__DistributesOver'737'__16 ::
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d__DistributesOver'737'__16 = erased
-- Data.Nat.Binary.Properties._.Associative
d_Associative_32 ::
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_Associative_32 = erased
-- Data.Nat.Binary.Properties._.Commutative
d_Commutative_36 ::
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_Commutative_36 = erased
-- Data.Nat.Binary.Properties._.Identity
d_Identity_52 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_Identity_52 = erased
-- Data.Nat.Binary.Properties._.LeftCancellative
d_LeftCancellative_66 ::
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_LeftCancellative_66 = erased
-- Data.Nat.Binary.Properties._.LeftIdentity
d_LeftIdentity_78 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_LeftIdentity_78 = erased
-- Data.Nat.Binary.Properties._.LeftZero
d_LeftZero_86 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_LeftZero_86 = erased
-- Data.Nat.Binary.Properties._.RightCancellative
d_RightCancellative_96 ::
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_RightCancellative_96 = erased
-- Data.Nat.Binary.Properties._.RightIdentity
d_RightIdentity_108 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_RightIdentity_108 = erased
-- Data.Nat.Binary.Properties._.RightZero
d_RightZero_116 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_RightZero_116 = erased
-- Data.Nat.Binary.Properties._.Zero
d_Zero_136 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
   MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8) ->
  ()
d_Zero_136 = erased
-- Data.Nat.Binary.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_152 a0 a1 = ()
-- Data.Nat.Binary.Properties._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_156 a0 = ()
-- Data.Nat.Binary.Properties._.IsCommutativeSemiring
d_IsCommutativeSemiring_158 a0 a1 a2 a3 = ()
-- Data.Nat.Binary.Properties._.IsMagma
d_IsMagma_184 a0 = ()
-- Data.Nat.Binary.Properties._.IsMonoid
d_IsMonoid_190 a0 a1 = ()
-- Data.Nat.Binary.Properties._.IsSemigroup
d_IsSemigroup_212 a0 = ()
-- Data.Nat.Binary.Properties._.IsSemiring
d_IsSemiring_216 a0 a1 a2 a3 = ()
-- Data.Nat.Binary.Properties._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_218 a0 a1 a2 a3 = ()
-- Data.Nat.Binary.Properties._.IsCommutativeMonoid.comm
d_comm_522 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_522 = erased
-- Data.Nat.Binary.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_538 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_538 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v0)
-- Data.Nat.Binary.Properties._.IsCommutativeSemigroup.comm
d_comm_690 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_690 = erased
-- Data.Nat.Binary.Properties._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_700 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_700 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_554 (coe v0)
-- Data.Nat.Binary.Properties._.IsCommutativeSemiring.*-comm
d_'42''45'comm_722 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_722 = erased
-- Data.Nat.Binary.Properties._.IsCommutativeSemiring.isSemiring
d_isSemiring_792 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_792 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v0)
-- Data.Nat.Binary.Properties._.IsMagma.isEquivalence
d_isEquivalence_1494 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1494 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v0)
-- Data.Nat.Binary.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1508 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1508 = erased
-- Data.Nat.Binary.Properties._.IsMonoid.identity
d_identity_1604 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1604 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_696 (coe v0)
-- Data.Nat.Binary.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1616 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_1616 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v0)
-- Data.Nat.Binary.Properties._.IsSemigroup.assoc
d_assoc_2350 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2350 = erased
-- Data.Nat.Binary.Properties._.IsSemigroup.isMagma
d_isMagma_2354 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2354 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v0)
-- Data.Nat.Binary.Properties._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2468 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_2468 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
      (coe v0)
-- Data.Nat.Binary.Properties._.IsSemiring.zero
d_zero_2482 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2482 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1604 (coe v0)
-- Data.Nat.Binary.Properties._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2490 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2490 = erased
-- Data.Nat.Binary.Properties._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2492 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2492 = erased
-- Data.Nat.Binary.Properties._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2498 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2498 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1512 (coe v0)
-- Data.Nat.Binary.Properties._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2528 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'isCommutativeMonoid_2528 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
      (coe v0)
-- Data.Nat.Binary.Properties._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2540 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2540 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1514 (coe v0)
-- Data.Nat.Binary.Properties.2[1+x]≢0
d_2'91'1'43'x'93''8802'0_2816 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_2'91'1'43'x'93''8802'0_2816 = erased
-- Data.Nat.Binary.Properties.1+[2x]≢0
d_1'43''91'2x'93''8802'0_2818 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43''91'2x'93''8802'0_2818 = erased
-- Data.Nat.Binary.Properties.2[1+_]-injective
d_2'91'1'43'_'93''45'injective_2820 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'91'1'43'_'93''45'injective_2820 = erased
-- Data.Nat.Binary.Properties.1+[2_]-injective
d_1'43''91'2_'93''45'injective_2822 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'43''91'2_'93''45'injective_2822 = erased
-- Data.Nat.Binary.Properties._≟_
d__'8799'__2824 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__2824 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased erased (coe d__'8799'__2824 (coe v2) (coe v3))
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased erased (coe d__'8799'__2824 (coe v2) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.≡-isDecEquivalence
d_'8801''45'isDecEquivalence_2834 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8801''45'isDecEquivalence_2834
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isDecEquivalence_398
      (coe d__'8799'__2824)
-- Data.Nat.Binary.Properties.≡-setoid
d_'8801''45'setoid_2836 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8801''45'setoid_2836
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Nat.Binary.Properties.≡-decSetoid
d_'8801''45'decSetoid_2838 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86
d_'8801''45'decSetoid_2838
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__2824)
-- Data.Nat.Binary.Properties.toℕ-double
d_toℕ'45'double_2842 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'double_2842 = erased
-- Data.Nat.Binary.Properties.toℕ-suc
d_toℕ'45'suc_2854 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'suc_2854 = erased
-- Data.Nat.Binary.Properties.toℕ-pred
d_toℕ'45'pred_2864 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'pred_2864 = erased
-- Data.Nat.Binary.Properties.toℕ-fromℕ'
d_toℕ'45'fromℕ''_2870 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'fromℕ''_2870 = erased
-- Data.Nat.Binary.Properties.fromℕ≡fromℕ'
d_fromℕ'8801'fromℕ''_2878 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'8801'fromℕ''_2878 = erased
-- Data.Nat.Binary.Properties._.split
d_split_2886 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_split_2886 ~v0 v1 = du_split_2886 v1
du_split_2886 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_split_2886 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v0)
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
             (coe v1)
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties._.head
d_head_2892 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Maybe Bool
d_head_2892 ~v0 v1 = du_head_2892 v1
du_head_2892 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Maybe Bool
du_head_2892 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_split_2886 (coe v0))
-- Data.Nat.Binary.Properties._.tail
d_tail_2894 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_tail_2894 ~v0 v1 = du_tail_2894 v1
du_tail_2894 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_tail_2894 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe du_split_2886 (coe v0))
-- Data.Nat.Binary.Properties._.split-injective
d_split'45'injective_2896 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split'45'injective_2896 = erased
-- Data.Nat.Binary.Properties._.split-if
d_split'45'if_2902 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split'45'if_2902 = erased
-- Data.Nat.Binary.Properties._.head-suc
d_head'45'suc_2910 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_head'45'suc_2910 = erased
-- Data.Nat.Binary.Properties._.tail-suc
d_tail'45'suc_2918 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tail'45'suc_2918 = erased
-- Data.Nat.Binary.Properties._.head-homo
d_head'45'homo_2926 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_head'45'homo_2926 = erased
-- Data.Nat.Binary.Properties._.tail-homo
d_tail'45'homo_2932 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tail'45'homo_2932 = erased
-- Data.Nat.Binary.Properties._.fromℕ-helper≡fromℕ'
d_fromℕ'45'helper'8801'fromℕ''_2940 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'45'helper'8801'fromℕ''_2940 = erased
-- Data.Nat.Binary.Properties._._.rec-n/2
d_rec'45'n'47'2_2956 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rec'45'n'47'2_2956 = erased
-- Data.Nat.Binary.Properties.toℕ-fromℕ
d_toℕ'45'fromℕ_2960 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'fromℕ_2960 = erased
-- Data.Nat.Binary.Properties.toℕ-injective
d_toℕ'45'injective_2968 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'injective_2968 = erased
-- Data.Nat.Binary.Properties._.1+xN≡1+yN
d_1'43'xN'8801'1'43'yN_2980 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'43'xN'8801'1'43'yN_2980 = erased
-- Data.Nat.Binary.Properties._.xN≡yN
d_xN'8801'yN_2982 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xN'8801'yN_2982 = erased
-- Data.Nat.Binary.Properties._.x≡y
d_x'8801'y_2984 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'y_2984 = erased
-- Data.Nat.Binary.Properties._.2xN≡2yN
d_2xN'8801'2yN_3008 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2xN'8801'2yN_3008 = erased
-- Data.Nat.Binary.Properties._.xN≡yN
d_xN'8801'yN_3010 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xN'8801'yN_3010 = erased
-- Data.Nat.Binary.Properties._.x≡y
d_x'8801'y_3012 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'y_3012 = erased
-- Data.Nat.Binary.Properties.toℕ-surjective
d_toℕ'45'surjective_3014 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_toℕ'45'surjective_3014
  = coe
      MAlonzo.Code.Function.Consequences.Propositional.du_strictlySurjective'8658'surjective_40
      MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
      (\ v0 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (coe v0))
           erased)
-- Data.Nat.Binary.Properties.toℕ-isRelHomomorphism
d_toℕ'45'isRelHomomorphism_3018 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelHomomorphism_42
d_toℕ'45'isRelHomomorphism_3018
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsRelHomomorphism'46'constructor_587
      erased
-- Data.Nat.Binary.Properties.fromℕ-injective
d_fromℕ'45'injective_3020 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'45'injective_3020 = erased
-- Data.Nat.Binary.Properties.fromℕ-toℕ
d_fromℕ'45'toℕ_3032 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'45'toℕ_3032 = erased
-- Data.Nat.Binary.Properties.toℕ-inverseˡ
d_toℕ'45'inverse'737'_3034 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inverse'737'_3034 = erased
-- Data.Nat.Binary.Properties.toℕ-inverseʳ
d_toℕ'45'inverse'691'_3036 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inverse'691'_3036 = erased
-- Data.Nat.Binary.Properties.toℕ-inverseᵇ
d_toℕ'45'inverse'7495'_3038 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_toℕ'45'inverse'7495'_3038
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Binary.Properties.fromℕ-pred
d_fromℕ'45'pred_3042 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'45'pred_3042 = erased
-- Data.Nat.Binary.Properties._.y
d_y_3050 ::
  Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_y_3050 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (coe v0)
-- Data.Nat.Binary.Properties.x≡0⇒toℕ[x]≡0
d_x'8801'0'8658'toℕ'91'x'93''8801'0_3052 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'0'8658'toℕ'91'x'93''8801'0_3052 = erased
-- Data.Nat.Binary.Properties.toℕ[x]≡0⇒x≡0
d_toℕ'91'x'93''8801'0'8658'x'8801'0_3054 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'91'x'93''8801'0'8658'x'8801'0_3054 = erased
-- Data.Nat.Binary.Properties.x≮0
d_x'8814'0_3056 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x'8814'0_3056 = erased
-- Data.Nat.Binary.Properties.x≢0⇒x>0
d_x'8802'0'8658'x'62'0_3058 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_x'8802'0'8658'x'62'0_3058 v0 ~v1
  = du_x'8802'0'8658'x'62'0_3058 v0
du_x'8802'0'8658'x'62'0_3058 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_x'8802'0'8658'x'62'0_3058 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v1
        -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'even_20
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v1
        -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'odd_24
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.1+[2x]<2[1+x]
d_1'43''91'2x'93''60'2'91'1'43'x'93'_3064 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_1'43''91'2x'93''60'2'91'1'43'x'93'_3064 ~v0
  = du_1'43''91'2x'93''60'2'91'1'43'x'93'_3064
du_1'43''91'2x'93''60'2'91'1'43'x'93'_3064 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_1'43''91'2x'93''60'2'91'1'43'x'93'_3064
  = coe
      MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
-- Data.Nat.Binary.Properties.<⇒≢
d_'60''8658''8802'_3068 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_3068 = erased
-- Data.Nat.Binary.Properties.>⇒≢
d_'62''8658''8802'_3074 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''8658''8802'_3074 = erased
-- Data.Nat.Binary.Properties.≡⇒≮
d_'8801''8658''8814'_3078 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8801''8658''8814'_3078 = erased
-- Data.Nat.Binary.Properties.≡⇒≯
d_'8801''8658''8815'_3084 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8801''8658''8815'_3084 = erased
-- Data.Nat.Binary.Properties.<⇒≯
d_'60''8658''8815'_3090 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8815'_3090 = erased
-- Data.Nat.Binary.Properties.>⇒≮
d_'62''8658''8814'_3112 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''8658''8814'_3112 = erased
-- Data.Nat.Binary.Properties.<⇒≤
d_'60''8658''8804'_3116 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'60''8658''8804'_3116 ~v0 ~v1 = du_'60''8658''8804'_3116
du_'60''8658''8804'_3116 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'60''8658''8804'_3116
  = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Data.Nat.Binary.Properties.toℕ-mono-<
d_toℕ'45'mono'45''60'_3118 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'mono'45''60'_3118 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.Nat.Properties.du_0'60'1'43'n_3130)
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v4
               -> case coe v2 of
                    MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30 v7
                      -> coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                              (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864)
                              (\ v8 v9 v10 ->
                                 coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2912 v10))
                           (addInt
                              (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                 MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v8 v9 -> v8) v0 v1))
                           (coe
                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                              (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                 (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864)
                                 (\ v8 v9 v10 v11 v12 ->
                                    coe
                                      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3042
                                      v11 v12))
                              (addInt
                                 (coe (1 :: Integer))
                                 (coe
                                    mulInt (coe (2 :: Integer))
                                    (coe addInt (coe (1 :: Integer)) (coe du_xN_3130 (coe v3)))))
                              (addInt
                                 (coe (1 :: Integer))
                                 (coe mulInt (coe (2 :: Integer)) (coe du_yN_3132 (coe v4))))
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864)
                                    (\ v8 v9 v10 v11 v12 ->
                                       coe
                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3042
                                         v11 v12))
                                 (addInt
                                    (coe (1 :: Integer))
                                    (coe mulInt (coe (2 :: Integer)) (coe du_yN_3132 (coe v4))))
                                 (addInt
                                    (coe (2 :: Integer))
                                    (coe mulInt (coe (2 :: Integer)) (coe du_yN_3132 (coe v4))))
                                 (coe
                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                    (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0
                                    v1)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                    (\ v8 v9 v10 v11 v12 -> v12)
                                    (addInt
                                       (coe (2 :: Integer))
                                       (coe mulInt (coe (2 :: Integer)) (coe du_yN_3132 (coe v4))))
                                    (mulInt
                                       (coe (2 :: Integer))
                                       (coe addInt (coe (1 :: Integer)) (coe du_yN_3132 (coe v4))))
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                       v0 v1)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                          (coe
                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864))
                                       (coe
                                          mulInt (coe (2 :: Integer))
                                          (coe
                                             addInt (coe (1 :: Integer))
                                             (coe du_yN_3132 (coe v4)))))
                                    erased)
                                 (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2902
                                    (coe
                                       addInt (coe (1 :: Integer))
                                       (coe
                                          mulInt (coe (2 :: Integer)) (coe du_yN_3132 (coe v4))))))
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3598
                                 (1 :: Integer)
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    (mulInt (coe (2 :: Integer))) (\ v8 v9 -> v8)
                                    (addInt
                                       (coe (1 :: Integer))
                                       (coe
                                          MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                          MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                          (\ v8 v9 -> v8) v3 v4))
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                       v3 v4))
                                 (coe
                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                    (\ v8 v9 -> v9) (mulInt (coe (2 :: Integer)))
                                    (addInt
                                       (coe (1 :: Integer))
                                       (coe
                                          MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                          MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                          (\ v8 v9 -> v8) v3 v4))
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                       v3 v4))
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4138
                                    (2 :: Integer)
                                    (addInt
                                       (coe (1 :: Integer))
                                       (coe
                                          MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                          MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                          (\ v8 v9 -> v8) v3 v4))
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                       v3 v4)
                                    (d_xN'60'yN_3134 (coe v3) (coe v4) (coe v7)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v4
               -> case coe v2 of
                    MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36 v7
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3598
                           (1 :: Integer)
                           (coe
                              MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                              (mulInt (coe (2 :: Integer))) (\ v8 v9 -> v8)
                              (addInt
                                 (coe (1 :: Integer))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v8 v9 -> v8) v3
                                    v4))
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v3 v4))
                           (coe
                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                              (\ v8 v9 -> v9) (mulInt (coe (2 :: Integer)))
                              (addInt
                                 (coe (1 :: Integer))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v8 v9 -> v8) v3
                                    v4))
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v3 v4))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4138
                              (2 :: Integer)
                              (addInt
                                 (coe (1 :: Integer))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v8 v9 -> v8) v3
                                    v4))
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v3 v4)
                              (d_toℕ'45'mono'45''60'_3118 (coe v3) (coe v4) (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v4
               -> case coe v2 of
                    MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42 v7
                      -> case coe v7 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                             -> coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                     (coe
                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864)
                                     (\ v9 v10 v11 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2912
                                          v11))
                                  (addInt
                                     (coe (1 :: Integer))
                                     (coe
                                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v9 v10 -> v9)
                                        v0 v1))
                                  (coe
                                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                     (\ v9 v10 -> v10) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                     v0 v1)
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                     (\ v9 v10 v11 v12 v13 -> v13)
                                     (addInt
                                        (coe (2 :: Integer))
                                        (coe mulInt (coe (2 :: Integer)) (coe du_xN_3152 (coe v3))))
                                     (mulInt
                                        (coe (2 :: Integer))
                                        (coe addInt (coe (1 :: Integer)) (coe du_xN_3152 (coe v3))))
                                     (coe
                                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                        (\ v9 v10 -> v10)
                                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                           (coe
                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864)
                                           (\ v9 v10 v11 v12 v13 ->
                                              coe
                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3042
                                                v12 v13))
                                        (mulInt
                                           (coe (2 :: Integer))
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe du_xN_3152 (coe v3))))
                                        (mulInt (coe (2 :: Integer)) (coe du_yN_3154 (coe v4)))
                                        (coe
                                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                           (\ v9 v10 -> v10)
                                           MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864)
                                              (\ v9 v10 v11 v12 v13 ->
                                                 coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3042
                                                   v12 v13))
                                           (mulInt (coe (2 :: Integer)) (coe du_yN_3154 (coe v4)))
                                           (mulInt
                                              (coe (2 :: Integer))
                                              (coe
                                                 addInt (coe (1 :: Integer))
                                                 (coe du_yN_3154 (coe v4))))
                                           (coe
                                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                              (\ v9 v10 -> v10)
                                              MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                 (coe
                                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864))
                                              (coe
                                                 mulInt (coe (2 :: Integer))
                                                 (coe
                                                    addInt (coe (1 :: Integer))
                                                    (coe du_yN_3154 (coe v4)))))
                                           (coe
                                              MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4138
                                              (2 :: Integer)
                                              (MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v4))
                                              (addInt
                                                 (coe (1 :: Integer))
                                                 (coe
                                                    MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                                    (coe v4)))
                                              (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2902
                                                 (coe
                                                    MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                                    (coe v4)))))
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4138
                                           (2 :: Integer)
                                           (addInt
                                              (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                 MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                                                 (\ v9 v10 -> v9) v3 v4))
                                           (coe
                                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                              (\ v9 v10 -> v10)
                                              MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v3 v4)
                                           (d_xN'60'yN_3156 (coe v3) (coe v4) (coe v8))))
                                     erased)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                             -> coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2810
                                  (coe
                                     addInt (coe (1 :: Integer))
                                     (coe
                                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v9 v10 -> v9)
                                        v0
                                        (coe
                                           MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12
                                           (coe v3))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v4
               -> case coe v2 of
                    MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48 v7
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3628
                           (coe (1 :: Integer))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'691''45''60'_4168
                              (coe (2 :: Integer))
                              (coe
                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                 (\ v8 v9 -> v9) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v3 v4)
                              (coe d_xN'60'yN_3174 (coe v3) (coe v4) (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties._.xN
d_xN_3130 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 -> Integer
d_xN_3130 v0 ~v1 ~v2 = du_xN_3130 v0
du_xN_3130 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_xN_3130 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.yN
d_yN_3132 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 -> Integer
d_yN_3132 ~v0 v1 ~v2 = du_yN_3132 v1
du_yN_3132 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_yN_3132 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.xN<yN
d_xN'60'yN_3134 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_xN'60'yN_3134 v0 v1 v2
  = coe d_toℕ'45'mono'45''60'_3118 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties._.xN
d_xN_3152 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 -> Integer
d_xN_3152 v0 ~v1 ~v2 = du_xN_3152 v0
du_xN_3152 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_xN_3152 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.yN
d_yN_3154 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 -> Integer
d_yN_3154 ~v0 v1 ~v2 = du_yN_3154 v1
du_yN_3154 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_yN_3154 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.xN<yN
d_xN'60'yN_3156 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_xN'60'yN_3156 v0 v1 v2
  = coe d_toℕ'45'mono'45''60'_3118 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties._.xN<yN
d_xN'60'yN_3174 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_xN'60'yN_3174 v0 v1 v2
  = coe d_toℕ'45'mono'45''60'_3118 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties.toℕ-cancel-<
d_toℕ'45'cancel'45''60'_3180 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_toℕ'45'cancel'45''60'_3180 v0 v1 ~v2
  = du_toℕ'45'cancel'45''60'_3180 v0 v1
du_toℕ'45'cancel'45''60'_3180 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_toℕ'45'cancel'45''60'_3180 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v2
               -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'even_20
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v2
               -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'odd_24
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v3
               -> coe
                    MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30
                    (coe du_toℕ'45'cancel'45''60'_3180 (coe v2) (coe v3))
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v3
               -> coe
                    MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36
                    (coe du_toℕ'45'cancel'45''60'_3180 (coe v2) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2700
                                 (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v2)))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                               (coe
                                  eqInt (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v2))
                                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v3)))) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
                                        (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
                                        (coe
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                           (coe du_toℕ'45'cancel'45''60'_3180 (coe v2) (coe v3))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v3
               -> coe
                    MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48
                    (coe du_toℕ'45'cancel'45''60'_3180 (coe v2) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.fromℕ-cancel-<
d_fromℕ'45'cancel'45''60'_3246 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℕ'45'cancel'45''60'_3246 v0 v1 v2
  = coe
      d_toℕ'45'mono'45''60'_3118
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (coe v0))
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (coe v1))
      (coe v2)
-- Data.Nat.Binary.Properties.fromℕ-mono-<
d_fromℕ'45'mono'45''60'_3248 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_fromℕ'45'mono'45''60'_3248 v0 v1 ~v2
  = du_fromℕ'45'mono'45''60'_3248 v0 v1
du_fromℕ'45'mono'45''60'_3248 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_fromℕ'45'mono'45''60'_3248 v0 v1
  = coe
      du_toℕ'45'cancel'45''60'_3180
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (\ v2 v3 -> v2) v0
         v1)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v2 v3 -> v3) MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 v0
         v1)
-- Data.Nat.Binary.Properties.toℕ-isHomomorphism-<
d_toℕ'45'isHomomorphism'45''60'_3250 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsOrderHomomorphism_138
d_toℕ'45'isHomomorphism'45''60'_3250
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsOrderHomomorphism'46'constructor_5435
      erased (coe d_toℕ'45'mono'45''60'_3118)
-- Data.Nat.Binary.Properties.toℕ-isMonomorphism-<
d_toℕ'45'isMonomorphism'45''60'_3252 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsOrderMonomorphism_182
d_toℕ'45'isMonomorphism'45''60'_3252
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsOrderMonomorphism'46'constructor_9103
      (coe d_toℕ'45'isHomomorphism'45''60'_3250) erased
      (\ v0 v1 v2 -> coe du_toℕ'45'cancel'45''60'_3180 v0 v1)
-- Data.Nat.Binary.Properties.<-irrefl
d_'60''45'irrefl_3254 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_3254 = erased
-- Data.Nat.Binary.Properties.<-trans
d_'60''45'trans_3260 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'60''45'trans_3260 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> case coe v2 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v5
               -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'even_20
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v5
               -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'odd_24
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30 v8
               -> case coe v1 of
                    MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v9
                      -> case coe v4 of
                           MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30 v12
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v13
                                    -> coe
                                         MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30
                                         (d_'60''45'trans_3260
                                            (coe v5) (coe v9) (coe v13) (coe v8) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36 v12
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v13
                                    -> coe
                                         MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36
                                         (d_'60''45'trans_3260
                                            (coe v5) (coe v9) (coe v13) (coe v8) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36 v8
               -> case coe v1 of
                    MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v9
                      -> case coe v4 of
                           MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42 v12
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v13
                                    -> case coe v12 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30
                                                (d_'60''45'trans_3260
                                                   (coe v5) (coe v9) (coe v13) (coe v8) (coe v14))
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30
                                                v8
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48 v12
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v13
                                    -> coe
                                         MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36
                                         (d_'60''45'trans_3260
                                            (coe v5) (coe v9) (coe v13) (coe v8) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42 v8
               -> case coe v1 of
                    MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v9
                      -> case coe v8 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                             -> case coe v4 of
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30 v13
                                    -> case coe v2 of
                                         MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v14
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
                                                (coe
                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                   (coe
                                                      d_'60''45'trans_3260 (coe v5) (coe v9)
                                                      (coe v14) (coe v10) (coe v13)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36 v13
                                    -> case coe v2 of
                                         MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v14
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48
                                                (d_'60''45'trans_3260
                                                   (coe v5) (coe v9) (coe v14) (coe v10) (coe v13))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                             -> case coe v4 of
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30 v13
                                    -> coe
                                         MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
                                         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13))
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36 v13
                                    -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48 v13
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48 v8
               -> case coe v1 of
                    MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v9
                      -> case coe v4 of
                           MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42 v12
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v13
                                    -> case coe v12 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
                                                (coe
                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                   (coe
                                                      d_'60''45'trans_3260 (coe v5) (coe v9)
                                                      (coe v13) (coe v8) (coe v14)))
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                           -> coe
                                                MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
                                                (coe
                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                   (coe v8))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48 v12
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v13
                                    -> coe
                                         MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48
                                         (d_'60''45'trans_3260
                                            (coe v5) (coe v9) (coe v13) (coe v8) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.<-asym
d_'60''45'asym_3302 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_3302 = erased
-- Data.Nat.Binary.Properties.<-cmp
d_'60''45'cmp_3308 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_3308 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v2
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                    (coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'even_20)
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v2
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                    (coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'odd_24)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'even_20)
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v3
               -> let v4 = d_'60''45'cmp_3308 (coe v2) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v5
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe du_lt_3328 (coe v5))
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v6
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe du_gt_3344 (coe v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v3
               -> let v4 = d_'60''45'cmp_3308 (coe v2) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v5
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe du_lt_3364 (coe v5))
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v6
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe du_gt_3374)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe du_gt_3388 (coe v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe du_gt_3394)
             MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v3
               -> let v4 = d_'60''45'cmp_3308 (coe v2) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v5
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe du_lt_3414 (coe v5))
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v6
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe du_lt_3426 erased)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe du_gt_3438 (coe v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v3
               -> let v4 = d_'60''45'cmp_3308 (coe v2) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v5
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe du_lt_3458 (coe v5))
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v6
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe du_gt_3474 (coe v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties._.lt
d_lt_3328 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_lt_3328 ~v0 ~v1 v2 ~v3 ~v4 = du_lt_3328 v2
du_lt_3328 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_lt_3328 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30 v0
-- Data.Nat.Binary.Properties._.gt
d_gt_3344 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_gt_3344 ~v0 ~v1 ~v2 ~v3 v4 = du_gt_3344 v4
du_gt_3344 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_gt_3344 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30 v0
-- Data.Nat.Binary.Properties._.lt
d_lt_3364 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_lt_3364 ~v0 ~v1 v2 ~v3 ~v4 = du_lt_3364 v2
du_lt_3364 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_lt_3364 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36 v0
-- Data.Nat.Binary.Properties._.gt
d_gt_3374 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_gt_3374 ~v0 ~v1 ~v2 = du_gt_3374
du_gt_3374 :: MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_gt_3374 = coe du_1'43''91'2x'93''60'2'91'1'43'x'93'_3064
-- Data.Nat.Binary.Properties._.gt
d_gt_3388 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_gt_3388 ~v0 ~v1 ~v2 ~v3 v4 = du_gt_3388 v4
du_gt_3388 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_gt_3388 v0
  = coe
      MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0))
-- Data.Nat.Binary.Properties._.gt
d_gt_3394 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_gt_3394 ~v0 = du_gt_3394
du_gt_3394 :: MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_gt_3394 = coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'odd_24
-- Data.Nat.Binary.Properties._.lt
d_lt_3414 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_lt_3414 ~v0 ~v1 v2 ~v3 ~v4 = du_lt_3414 v2
du_lt_3414 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_lt_3414 v0
  = coe
      MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0))
-- Data.Nat.Binary.Properties._.lt
d_lt_3426 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_lt_3426 ~v0 ~v1 ~v2 v3 ~v4 = du_lt_3426 v3
du_lt_3426 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_lt_3426 v0
  = coe
      MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v0))
-- Data.Nat.Binary.Properties._.gt
d_gt_3438 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_gt_3438 ~v0 ~v1 ~v2 ~v3 v4 = du_gt_3438 v4
du_gt_3438 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_gt_3438 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36 v0
-- Data.Nat.Binary.Properties._.lt
d_lt_3458 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_lt_3458 ~v0 ~v1 v2 ~v3 ~v4 = du_lt_3458 v2
du_lt_3458 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_lt_3458 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48 v0
-- Data.Nat.Binary.Properties._.gt
d_gt_3474 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_gt_3474 ~v0 ~v1 ~v2 ~v3 v4 = du_gt_3474 v4
du_gt_3474 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_gt_3474 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48 v0
-- Data.Nat.Binary.Properties._<?_
d__'60''63'__3476 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__3476
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_tri'8658'dec'60'_584
      (coe d_'60''45'cmp_3308)
-- Data.Nat.Binary.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_3478 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_354
d_'60''45'isStrictPartialOrder_3478
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_16311
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      d_'60''45'trans_3260
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
-- Data.Nat.Binary.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_3480 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_600
d_'60''45'isStrictTotalOrder_3480
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_27253
      (coe d_'60''45'isStrictPartialOrder_3478) (coe d_'60''45'cmp_3308)
-- Data.Nat.Binary.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_3482 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_744
d_'60''45'strictPartialOrder_3482
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_14243
      d_'60''45'isStrictPartialOrder_3478
-- Data.Nat.Binary.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_3484 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1256
d_'60''45'strictTotalOrder_3484
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_24345
      d_'60''45'isStrictTotalOrder_3480
-- Data.Nat.Binary.Properties.x<2[1+x]
d_x'60'2'91'1'43'x'93'_3488 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_x'60'2'91'1'43'x'93'_3488 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'even_20
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v1
        -> coe
             MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'even_30
             (d_x'60'2'91'1'43'x'93'_3488 (coe v1))
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v1
        -> coe
             MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'even_42
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe d_x'60'1'43''91'2x'93'_3492 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.x<1+[2x]
d_x'60'1'43''91'2x'93'_3492 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_x'60'1'43''91'2x'93'_3492 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'odd_24
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v1
        -> coe
             MAlonzo.Code.Data.Nat.Binary.Base.C_even'60'odd_36
             (d_x'60'2'91'1'43'x'93'_3488 (coe v1))
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v1
        -> coe
             MAlonzo.Code.Data.Nat.Binary.Base.C_odd'60'odd_48
             (d_x'60'1'43''91'2x'93'_3492 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.<⇒≱
d_'60''8658''8817'_3502 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_3502 = erased
-- Data.Nat.Binary.Properties.≤⇒≯
d_'8804''8658''8815'_3512 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_3512 = erased
-- Data.Nat.Binary.Properties.≮⇒≥
d_'8814''8658''8805'_3518 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8814''8658''8805'_3518 v0 v1 ~v2
  = du_'8814''8658''8805'_3518 v0 v1
du_'8814''8658''8805'_3518 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8814''8658''8805'_3518 v0 v1
  = let v2 = d_'60''45'cmp_3308 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v3
           -> coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v4
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v5
           -> coe du_'60''8658''8804'_3116 v5
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Binary.Properties.≰⇒>
d_'8816''8658''62'_3554 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'8816''8658''62'_3554 v0 v1 ~v2 = du_'8816''8658''62'_3554 v0 v1
du_'8816''8658''62'_3554 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'8816''8658''62'_3554 v0 v1
  = let v2 = d_'60''45'cmp_3308 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v3
           -> coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v4
           -> coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v5 -> coe v5
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Binary.Properties.≤∧≢⇒<
d_'8804''8743''8802''8658''60'_3594 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'8804''8743''8802''8658''60'_3594 ~v0 ~v1 v2 ~v3
  = du_'8804''8743''8802''8658''60'_3594 v2
du_'8804''8743''8802''8658''60'_3594 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'8804''8743''8802''8658''60'_3594 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.0≤x
d_0'8804'x_3604 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_0'8804'x_3604 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'even_20)
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Data.Nat.Binary.Base.C_0'60'odd_24)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.x≤0⇒x≡0
d_x'8804'0'8658'x'8801'0_3608 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8804'0'8658'x'8801'0_3608 = erased
-- Data.Nat.Binary.Properties.fromℕ-mono-≤
d_fromℕ'45'mono'45''8804'_3612 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_fromℕ'45'mono'45''8804'_3612 v0 v1 v2
  = let v3
          = MAlonzo.Code.Data.Nat.Properties.d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3164
              (coe v0) (coe v1)
              (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe du_fromℕ'45'mono'45''60'_3248 (coe v0) (coe v1))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Binary.Properties.toℕ-mono-≤
d_toℕ'45'mono'45''8804'_3628 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'mono'45''8804'_3628 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2912
             (coe d_toℕ'45'mono'45''60'_3118 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2810
             (coe
                MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v4 v5 -> v4) v0 v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.toℕ-cancel-≤
d_toℕ'45'cancel'45''8804'_3636 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_toℕ'45'cancel'45''8804'_3636 v0 v1 v2
  = coe
      d_fromℕ'45'mono'45''8804'_3612
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1)) (coe v2)
-- Data.Nat.Binary.Properties.fromℕ-cancel-≤
d_fromℕ'45'cancel'45''8804'_3642 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fromℕ'45'cancel'45''8804'_3642 v0 v1 v2
  = coe
      d_toℕ'45'mono'45''8804'_3628
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (coe v0))
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (coe v1))
      (coe v2)
-- Data.Nat.Binary.Properties.toℕ-isHomomorphism-≤
d_toℕ'45'isHomomorphism'45''8804'_3644 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsOrderHomomorphism_138
d_toℕ'45'isHomomorphism'45''8804'_3644
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsOrderHomomorphism'46'constructor_5435
      erased (coe d_toℕ'45'mono'45''8804'_3628)
-- Data.Nat.Binary.Properties.toℕ-isMonomorphism-≤
d_toℕ'45'isMonomorphism'45''8804'_3646 ::
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsOrderMonomorphism_182
d_toℕ'45'isMonomorphism'45''8804'_3646
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.C_IsOrderMonomorphism'46'constructor_9103
      (coe d_toℕ'45'isHomomorphism'45''8804'_3644) erased
      (coe d_toℕ'45'cancel'45''8804'_3636)
-- Data.Nat.Binary.Properties.≤-refl
d_'8804''45'refl_3648 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'refl_3648 ~v0 = du_'8804''45'refl_3648
du_'8804''45'refl_3648 :: MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''45'refl_3648
  = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Nat.Binary.Properties.≤-reflexive
d_'8804''45'reflexive_3650 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'reflexive_3650 ~v0 ~v1 ~v2
  = du_'8804''45'reflexive_3650
du_'8804''45'reflexive_3650 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''45'reflexive_3650 = coe du_'8804''45'refl_3648
-- Data.Nat.Binary.Properties.≤-trans
d_'8804''45'trans_3654 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'trans_3654 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict.du_trans_64
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
      (coe d_'60''45'trans_3260) (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties.<-≤-trans
d_'60''45''8804''45'trans_3662 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'60''45''8804''45'trans_3662 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe
             d_'60''45'trans_3260 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.≤-<-trans
d_'8804''45''60''45'trans_3676 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'8804''45''60''45'trans_3676 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe
             d_'60''45'trans_3260 (coe v0) (coe v1) (coe v2) (coe v5) (coe v4)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.≤-antisym
d_'8804''45'antisym_3684 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_3684 = erased
-- Data.Nat.Binary.Properties.≤-total
d_'8804''45'total_3686 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_3686 v0 v1
  = let v2 = d_'60''45'cmp_3308 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v3
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe du_'60''8658''8804'_3116 v3)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe du_'8804''45'reflexive_3650)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v5
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe du_'60''8658''8804'_3116 v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Binary.Properties._≤?_
d__'8804''63'__3714 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__3714 v0 v1
  = let v2 = d_'60''45'cmp_3308 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v3
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe
                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                   (coe du_'60''8658''8804'_3116 v3))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v4
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe
                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                   (coe du_'8804''45'reflexive_3650))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v5
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Binary.Properties.≤-isPreorder
d_'8804''45'isPreorder_3742 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_3742
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_3650)
      (coe d_'8804''45'trans_3654)
-- Data.Nat.Binary.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_3744 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_236
d_'8804''45'isPartialOrder_3744
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_11935
      (coe d_'8804''45'isPreorder_3742) erased
-- Data.Nat.Binary.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_3746 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_468
d_'8804''45'isTotalOrder_3746
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_22821
      (coe d_'8804''45'isPartialOrder_3744) (coe d_'8804''45'total_3686)
-- Data.Nat.Binary.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_3748 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_524
d_'8804''45'isDecTotalOrder_3748
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_24961
      (coe d_'8804''45'isTotalOrder_3746) (coe d__'8799'__2824)
      (coe d__'8804''63'__3714)
-- Data.Nat.Binary.Properties.≤-preorder
d_'8804''45'preorder_3750 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_136
d_'8804''45'preorder_3750
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2331
      d_'8804''45'isPreorder_3742
-- Data.Nat.Binary.Properties.≤-partialOrder
d_'8804''45'partialOrder_3752 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480
d_'8804''45'partialOrder_3752
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_9149
      d_'8804''45'isPartialOrder_3744
-- Data.Nat.Binary.Properties.≤-totalOrder
d_'8804''45'totalOrder_3754 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_966
d_'8804''45'totalOrder_3754
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_18801
      d_'8804''45'isTotalOrder_3746
-- Data.Nat.Binary.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_3756 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076
d_'8804''45'decTotalOrder_3756
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_21007
      d_'8804''45'isDecTotalOrder_3748
-- Data.Nat.Binary.Properties.≤-Reasoning._._IsRelatedTo_
d__IsRelatedTo__3762 a0 a1 = ()
-- Data.Nat.Binary.Properties.≤-Reasoning._._∎
d__'8718'_3764 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_3764
  = let v0 = d_'8804''45'isPreorder_3742 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
            (coe v0)))
-- Data.Nat.Binary.Properties.≤-Reasoning._.<-go
d_'60''45'go_3766 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_3766
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
      (coe d_'60''45'trans_3260)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
      (coe d_'60''45''8804''45'trans_3662)
-- Data.Nat.Binary.Properties.≤-Reasoning._.IsEquality
d_IsEquality_3768 a0 a1 a2 = ()
-- Data.Nat.Binary.Properties.≤-Reasoning._.IsEquality?
d_IsEquality'63'_3770 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_3770 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
      v2
-- Data.Nat.Binary.Properties.≤-Reasoning._.IsStrict
d_IsStrict_3772 a0 a1 a2 = ()
-- Data.Nat.Binary.Properties.≤-Reasoning._.IsStrict?
d_IsStrict'63'_3774 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_3774 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
      v2
-- Data.Nat.Binary.Properties.≤-Reasoning._.begin_
d_begin__3776 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_begin__3776
  = let v0 = d_'8804''45'isPreorder_3742 in
    coe
      (let v1 = \ v1 v2 -> coe du_'60''8658''8804'_3116 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe v0) (coe v1))))
-- Data.Nat.Binary.Properties.≤-Reasoning._.begin-contradiction_
d_begin'45'contradiction__3778 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d_begin'45'contradiction__3778 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
-- Data.Nat.Binary.Properties.≤-Reasoning._.begin_
d_begin__3780 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__3780 = erased
-- Data.Nat.Binary.Properties.≤-Reasoning._.begin_
d_begin__3782 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_begin__3782
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Data.Nat.Binary.Properties.≤-Reasoning._.eqRelation
d_eqRelation_3784 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_3784
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
-- Data.Nat.Binary.Properties.≤-Reasoning._.extractEquality
d_extractEquality_3788 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractEquality_3788 = erased
-- Data.Nat.Binary.Properties.≤-Reasoning._.extractStrict
d_extractStrict_3790 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_extractStrict_3790 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
      v2 v3
-- Data.Nat.Binary.Properties.≤-Reasoning._.start
d_start_3798 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_start_3798
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
      (coe d_'8804''45'isPreorder_3742)
      (\ v0 v1 -> coe du_'60''8658''8804'_3116)
-- Data.Nat.Binary.Properties.≤-Reasoning._.step-<
d_step'45''60'_3800 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_3800
  = let v0 = d_'60''45'trans_3260 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160 in
       coe
         (let v2 = d_'60''45''8804''45'trans_3662 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe v0) (coe v1) (coe v2)))))
-- Data.Nat.Binary.Properties.≤-Reasoning._.step-≡
d_step'45''8801'_3802 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_3802
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Binary.Properties.≤-Reasoning._.step-≡-∣
d_step'45''8801''45''8739'_3804 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_3804 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_3804 v2
du_step'45''8801''45''8739'_3804 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_3804 v0 = coe v0
-- Data.Nat.Binary.Properties.≤-Reasoning._.step-≡-⟨
d_step'45''8801''45''10216'_3806 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_3806
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Binary.Properties.≤-Reasoning._.step-≡-⟩
d_step'45''8801''45''10217'_3808 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_3808
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Binary.Properties.≤-Reasoning._.step-≡˘
d_step'45''8801''728'_3810 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_3810
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Binary.Properties.≤-Reasoning._.step-≤
d_step'45''8804'_3812 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_3812
  = let v0 = d_'8804''45'isPreorder_3742 in
    coe
      (let v1 = d_'8804''45''60''45'trans_3676 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe v0) (coe v1))))
-- Data.Nat.Binary.Properties.≤-Reasoning._.stop
d_stop_3814 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_3814
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
      (coe d_'8804''45'isPreorder_3742)
-- Data.Nat.Binary.Properties.≤-Reasoning._.strictRelation
d_strictRelation_3818 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_3818
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
-- Data.Nat.Binary.Properties.≤-Reasoning._.≈-go
d_'8776''45'go_3820 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_3820
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
      (coe d_'8804''45'isPreorder_3742)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
-- Data.Nat.Binary.Properties.≤-Reasoning._.≡-go
d_'8801''45'go_3822 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_3822 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_3822 v4
du_'8801''45'go_3822 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_3822 v0 = coe v0
-- Data.Nat.Binary.Properties.≤-Reasoning._.≤-go
d_'8804''45'go_3824 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_3824
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
      (coe d_'8804''45'isPreorder_3742)
      (coe d_'8804''45''60''45'trans_3676)
-- Data.Nat.Binary.Properties.<⇒<ℕ
d_'60''8658''60'ℕ_3846 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8658''60'ℕ_3846 v0 v1 v2
  = coe d_toℕ'45'mono'45''60'_3118 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties.<ℕ⇒<
d_'60'ℕ'8658''60'_3854 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'60'ℕ'8658''60'_3854 v0 v1 ~v2 = du_'60'ℕ'8658''60'_3854 v0 v1
du_'60'ℕ'8658''60'_3854 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'60'ℕ'8658''60'_3854 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v2) (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v3 v4 v5 v6 v7 -> v7) v0
            (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe d_'60''45'trans_3260)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (coe d_'60''45''8804''45'trans_3662))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1)))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1)))
                  v1 v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_3742))
                     (coe v1))
                  erased)
               (coe
                  du_fromℕ'45'mono'45''60'_3248
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v3 v4 -> v4) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0
                     v1)))
            erased))
-- Data.Nat.Binary.Properties.toℕ-homo-+
d_toℕ'45'homo'45''43'_3870 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'homo'45''43'_3870 = erased
-- Data.Nat.Binary.Properties._.m
d_m_3902 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_m_3902 v0 ~v1 = du_m_3902 v0
du_m_3902 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_3902 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n
d_n_3904 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_n_3904 ~v0 v1 = du_n_3904 v1
du_n_3904 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_3904 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.m
d_m_3920 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_m_3920 v0 ~v1 = du_m_3920 v0
du_m_3920 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_3920 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n
d_n_3922 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_n_3922 ~v0 v1 = du_n_3922 v1
du_n_3922 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_3922 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.m
d_m_3938 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_m_3938 v0 ~v1 = du_m_3938 v0
du_m_3938 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_3938 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n
d_n_3940 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_n_3940 ~v0 v1 = du_n_3940 v1
du_n_3940 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_3940 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties.toℕ-isMagmaHomomorphism-+
d_toℕ'45'isMagmaHomomorphism'45''43'_3948 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_188
d_toℕ'45'isMagmaHomomorphism'45''43'_3948
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMagmaHomomorphism'46'constructor_4629
      (coe d_toℕ'45'isRelHomomorphism_3018) erased
-- Data.Nat.Binary.Properties.toℕ-isMonoidHomomorphism-+
d_toℕ'45'isMonoidHomomorphism'45''43'_3950 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_362
d_toℕ'45'isMonoidHomomorphism'45''43'_3950
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidHomomorphism'46'constructor_9411
      (coe d_toℕ'45'isMagmaHomomorphism'45''43'_3948) erased
-- Data.Nat.Binary.Properties.toℕ-isMonoidMonomorphism-+
d_toℕ'45'isMonoidMonomorphism'45''43'_3952 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384
d_toℕ'45'isMonoidMonomorphism'45''43'_3952
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidMonomorphism'46'constructor_10237
      (coe d_toℕ'45'isMonoidHomomorphism'45''43'_3950) erased
-- Data.Nat.Binary.Properties.suc≗1+
d_suc'8791'1'43'_3956 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'8791'1'43'_3956 = erased
-- Data.Nat.Binary.Properties.suc-+
d_suc'45''43'_3962 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45''43'_3962 = erased
-- Data.Nat.Binary.Properties.1+≗suc
d_1'43''8791'suc_3988 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'43''8791'suc_3988 = erased
-- Data.Nat.Binary.Properties.fromℕ'-homo-+
d_fromℕ'''45'homo'45''43'_3994 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'''45'homo'45''43'_3994 = erased
-- Data.Nat.Binary.Properties._.a
d_a_4004 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_a_4004 v0 ~v1 = du_a_4004 v0
du_a_4004 ::
  Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_a_4004 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ''_168 (coe v0)
-- Data.Nat.Binary.Properties._.b
d_b_4006 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_b_4006 ~v0 v1 = du_b_4006 v1
du_b_4006 ::
  Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_b_4006 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ''_168 (coe v0)
-- Data.Nat.Binary.Properties.fromℕ-homo-+
d_fromℕ'45'homo'45''43'_4012 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'45'homo'45''43'_4012 = erased
-- Data.Nat.Binary.Properties.+-assoc
d_'43''45'assoc_4072 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_4072 = erased
-- Data.Nat.Binary.Properties.+-comm
d_'43''45'comm_4074 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_4074 = erased
-- Data.Nat.Binary.Properties.+-identityˡ
d_'43''45'identity'737'_4076 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737'_4076 = erased
-- Data.Nat.Binary.Properties.+-identityʳ
d_'43''45'identity'691'_4078 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_4078 = erased
-- Data.Nat.Binary.Properties.+-identity
d_'43''45'identity_4080 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'identity_4080
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Binary.Properties.+-cancelˡ-≡
d_'43''45'cancel'737''45''8801'_4082 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'737''45''8801'_4082 = erased
-- Data.Nat.Binary.Properties.+-cancelʳ-≡
d_'43''45'cancel'691''45''8801'_4084 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'691''45''8801'_4084 = erased
-- Data.Nat.Binary.Properties.+-isMagma
d_'43''45'isMagma_4086 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'43''45'isMagma_4086
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra.du_isMagma_14
-- Data.Nat.Binary.Properties.+-isSemigroup
d_'43''45'isSemigroup_4088 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'43''45'isSemigroup_4088
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSemigroup_268
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d_'43''45'0'45'rawMonoid_202))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
         (coe MAlonzo.Code.Data.Nat.Base.d_'43''45'0'45'rawMonoid_182))
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe d_toℕ'45'isMonoidMonomorphism'45''43'_3952))
      (coe MAlonzo.Code.Data.Nat.Properties.d_'43''45'isSemigroup_3374)
-- Data.Nat.Binary.Properties.+-isCommutativeSemigroup
d_'43''45'isCommutativeSemigroup_4090 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'43''45'isCommutativeSemigroup_4090
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemigroup'46'constructor_11565
      (coe d_'43''45'isSemigroup_4088) erased
-- Data.Nat.Binary.Properties.+-0-isMonoid
d_'43''45'0'45'isMonoid_4092 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'43''45'0'45'isMonoid_4092
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isMonoid_192
      (coe
         MAlonzo.Code.Data.Nat.Binary.Base.d_'43''45'0'45'rawMonoid_202)
      (coe MAlonzo.Code.Data.Nat.Base.d_'43''45'0'45'rawMonoid_182)
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150)
      (coe d_toℕ'45'isMonoidMonomorphism'45''43'_3952)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'43''45'0'45'isMonoid_3378)
-- Data.Nat.Binary.Properties.+-0-isCommutativeMonoid
d_'43''45'0'45'isCommutativeMonoid_4094 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'0'45'isCommutativeMonoid_4094
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isCommutativeMonoid_236
      (coe
         MAlonzo.Code.Data.Nat.Binary.Base.d_'43''45'0'45'rawMonoid_202)
      (coe MAlonzo.Code.Data.Nat.Base.d_'43''45'0'45'rawMonoid_182)
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150)
      (coe d_toℕ'45'isMonoidMonomorphism'45''43'_3952)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'0'45'isCommutativeMonoid_3380)
-- Data.Nat.Binary.Properties.+-magma
d_'43''45'magma_4096 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'43''45'magma_4096
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra.du_magma_20
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110)
-- Data.Nat.Binary.Properties.+-semigroup
d_'43''45'semigroup_4098 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'43''45'semigroup_4098
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9837
      MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
      d_'43''45'isSemigroup_4088
-- Data.Nat.Binary.Properties.+-commutativeSemigroup
d_'43''45'commutativeSemigroup_4100 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_'43''45'commutativeSemigroup_4100
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemigroup'46'constructor_12079
      MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
      d_'43''45'isCommutativeSemigroup_4090
-- Data.Nat.Binary.Properties.+-0-monoid
d_'43''45'0'45'monoid_4102 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'43''45'0'45'monoid_4102
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16201
      MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
      (coe MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10)
      d_'43''45'0'45'isMonoid_4092
-- Data.Nat.Binary.Properties.+-0-commutativeMonoid
d_'43''45'0'45'commutativeMonoid_4104 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''45'0'45'commutativeMonoid_4104
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
      MAlonzo.Code.Data.Nat.Binary.Base.d_0'7495'_180
      d_'43''45'0'45'isCommutativeMonoid_4094
-- Data.Nat.Binary.Properties.Bin+CSemigroup.[uv∙w]x≈u[vw∙x]
d_'91'uv'8729'w'93'x'8776'u'91'vw'8729'x'93'_4108 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'uv'8729'w'93'x'8776'u'91'vw'8729'x'93'_4108 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.[uv∙w]x≈u[v∙wx]
d_'91'uv'8729'w'93'x'8776'u'91'v'8729'wx'93'_4110 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'uv'8729'w'93'x'8776'u'91'v'8729'wx'93'_4110 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.[u∙vw]x≈u[v∙wx]
d_'91'u'8729'vw'93'x'8776'u'91'v'8729'wx'93'_4112 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'u'8729'vw'93'x'8776'u'91'v'8729'wx'93'_4112 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.[u∙vw]x≈uv∙wx
d_'91'u'8729'vw'93'x'8776'uv'8729'wx_4114 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'u'8729'vw'93'x'8776'uv'8729'wx_4114 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.alternative
d_alternative_4116 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alternative_4116
  = let v0 = d_'43''45'commutativeSemigroup_4100 in
    coe
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Algebra.Structures.d_assoc_480
                 (MAlonzo.Code.Algebra.Structures.d_isSemigroup_554
                    (coe
                       MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_686
                       (coe v0)))
                 v1 v1 v2))
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                 (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                    (coe
                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isSemigroup_554
                          (coe
                             MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_686
                             (coe v0)))))
                 (coe
                    MAlonzo.Code.Algebra.Bundles.d__'8729'__684 v0
                    (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__684 v0 v1 v2) v2)
                 (coe
                    MAlonzo.Code.Algebra.Bundles.d__'8729'__684 v0 v1
                    (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__684 v0 v2 v2))
                 (coe
                    MAlonzo.Code.Algebra.Structures.d_assoc_480
                    (MAlonzo.Code.Algebra.Structures.d_isSemigroup_554
                       (coe
                          MAlonzo.Code.Algebra.Bundles.d_isCommutativeSemigroup_686
                          (coe v0)))
                    v1 v2 v2))))
-- Data.Nat.Binary.Properties.Bin+CSemigroup.alternativeʳ
d_alternative'691'_4118 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'691'_4118 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.alternativeˡ
d_alternative'737'_4120 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'737'_4120 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.flexible
d_flexible_4122 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flexible_4122 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.interchange
d_interchange_4124 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_interchange_4124 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.middleSemimedial
d_middleSemimedial_4126 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_middleSemimedial_4126 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.semimedial
d_semimedial_4128 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semimedial_4128
  = coe
      MAlonzo.Code.Algebra.Properties.CommutativeSemigroup.du_semimedial_608
      (coe d_'43''45'commutativeSemigroup_4100)
-- Data.Nat.Binary.Properties.Bin+CSemigroup.semimedialʳ
d_semimedial'691'_4130 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'691'_4130 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.semimedialˡ
d_semimedial'737'_4132 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'737'_4132 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv∙wx≈u[vw∙x]
d_uv'8729'wx'8776'u'91'vw'8729'x'93'_4134 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8729'wx'8776'u'91'vw'8729'x'93'_4134 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈wx⇒u∙vy≈w∙xy
d_uv'8776'wx'8658'u'8729'vy'8776'w'8729'xy_4136 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'wx'8658'u'8729'vy'8776'w'8729'xy_4136 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈wx⇒yu∙vz≈yw∙xz
d_uv'8776'wx'8658'yu'8729'vz'8776'yw'8729'xz_4138 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'wx'8658'yu'8729'vz'8776'yw'8729'xz_4138 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈wx⇒yu∙v≈yw∙x
d_uv'8776'wx'8658'yu'8729'v'8776'yw'8729'x_4140 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'wx'8658'yu'8729'v'8776'yw'8729'x_4140 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒[xu∙v]y≈x∙wy
d_uv'8776'w'8658''91'xu'8729'v'93'y'8776'x'8729'wy_4142 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658''91'xu'8729'v'93'y'8776'x'8729'wy_4142 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒[xy∙u]v≈x∙yw
d_uv'8776'w'8658''91'xy'8729'u'93'v'8776'x'8729'yw_4144 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658''91'xy'8729'u'93'v'8776'x'8729'yw_4144 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒[x∙yu]v≈x∙yw
d_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_4146 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_4146 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒u[vx∙y]≈w∙xy
d_uv'8776'w'8658'u'91'vx'8729'y'93''8776'w'8729'xy_4148 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658'u'91'vx'8729'y'93''8776'w'8729'xy_4148 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒u∙vx≈wx
d_uv'8776'w'8658'u'8729'vx'8776'wx_4150 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658'u'8729'vx'8776'wx_4150 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒x[uv∙y]≈x∙wy
d_uv'8776'w'8658'x'91'uv'8729'y'93''8776'x'8729'wy_4152 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658'x'91'uv'8729'y'93''8776'x'8729'wy_4152 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒xu∙vy≈x∙wy
d_uv'8776'w'8658'xu'8729'vy'8776'x'8729'wy_4154 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658'xu'8729'vy'8776'x'8729'wy_4154 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒xu∙v≈xw
d_uv'8776'w'8658'xu'8729'v'8776'xw_4156 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658'xu'8729'v'8776'xw_4156 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒xy≈z⇒u[vx∙y]≈wz
d_uv'8776'w'8658'xy'8776'z'8658'u'91'vx'8729'y'93''8776'wz_4158 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658'xy'8776'z'8658'u'91'vx'8729'y'93''8776'wz_4158
  = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.uv≈w⇒x∙wy≈x∙[u∙vy]
d_uv'8776'w'8658'x'8729'wy'8776'x'8729''91'u'8729'vy'93'_4160 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uv'8776'w'8658'x'8729'wy'8776'x'8729''91'u'8729'vy'93'_4160
  = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙xx≈x∙yxx
d_xy'8729'xx'8776'x'8729'yxx_4162 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'xx'8776'x'8729'yxx_4162 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈xz∙y
d_xy'8729'z'8776'xz'8729'y_4164 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'xz'8729'y_4164 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈x∙zy
d_xy'8729'z'8776'x'8729'zy_4166 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'x'8729'zy_4166 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈yx∙z
d_xy'8729'z'8776'yx'8729'z_4168 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'yx'8729'z_4168 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈yz∙x
d_xy'8729'z'8776'yz'8729'x_4170 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'yz'8729'x_4170 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈y∙xz
d_xy'8729'z'8776'y'8729'xz_4172 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'y'8729'xz_4172 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈y∙zx
d_xy'8729'z'8776'y'8729'zx_4174 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'y'8729'zx_4174 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈zx∙y
d_xy'8729'z'8776'zx'8729'y_4176 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'zx'8729'y_4176 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈zy∙x
d_xy'8729'z'8776'zy'8729'x_4178 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'zy'8729'x_4178 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈z∙xy
d_xy'8729'z'8776'z'8729'xy_4180 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'z'8729'xy_4180 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.xy∙z≈z∙yx
d_xy'8729'z'8776'z'8729'yx_4182 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xy'8729'z'8776'z'8729'yx_4182 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈xy∙z
d_x'8729'yz'8776'xy'8729'z_4184 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'xy'8729'z_4184 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈xz∙y
d_x'8729'yz'8776'xz'8729'y_4186 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'xz'8729'y_4186 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈x∙zy
d_x'8729'yz'8776'x'8729'zy_4188 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'x'8729'zy_4188 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈yx∙z
d_x'8729'yz'8776'yx'8729'z_4190 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'yx'8729'z_4190 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈yz∙x
d_x'8729'yz'8776'yz'8729'x_4192 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'yz'8729'x_4192 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈y∙xz
d_x'8729'yz'8776'y'8729'xz_4194 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'y'8729'xz_4194 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈y∙zx
d_x'8729'yz'8776'y'8729'zx_4196 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'y'8729'zx_4196 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈zx∙y
d_x'8729'yz'8776'zx'8729'y_4198 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'zx'8729'y_4198 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈zy∙x
d_x'8729'yz'8776'zy'8729'x_4200 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'zy'8729'x_4200 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈z∙xy
d_x'8729'yz'8776'z'8729'xy_4202 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'z'8729'xy_4202 = erased
-- Data.Nat.Binary.Properties.Bin+CSemigroup.x∙yz≈z∙yx
d_x'8729'yz'8776'z'8729'yx_4204 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8729'yz'8776'z'8729'yx_4204 = erased
-- Data.Nat.Binary.Properties.+-mono-≤
d_'43''45'mono'45''8804'_4206 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'43''45'mono'45''8804'_4206 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v6 v7 -> coe du_'60''8658''8804'_3116))
      (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v2))
      (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
         (\ v6 v7 v8 v9 v10 -> v10)
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v2))
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe du_m_4224 (coe v0)))
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe du_n_4228 (coe v2))))
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v6 v7 v8 v9 v10 -> v10)
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe du_m_4224 (coe v0)))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe du_n_4228 (coe v2))))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe addInt (coe du_n_4228 (coe v2)) (coe du_m_4224 (coe v0))))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe d_'8804''45'isPreorder_3742)
                  (coe d_'8804''45''60''45'trans_3676))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe addInt (coe du_n_4228 (coe v2)) (coe du_m_4224 (coe v0))))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe
                     addInt (coe du_n'8242'_4230 (coe v3))
                     (coe du_m'8242'_4226 (coe v1))))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v6 v7 v8 v9 v10 -> v10)
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe
                        addInt (coe du_n'8242'_4230 (coe v3))
                        (coe du_m'8242'_4226 (coe v1))))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                        (coe du_m'8242'_4226 (coe v1)))
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                        (coe du_n'8242'_4230 (coe v3))))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v6 v7 v8 v9 v10 -> v10)
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                           (coe du_m'8242'_4226 (coe v1)))
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                           (coe du_n'8242'_4230 (coe v3))))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_3742))
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3)))
                     erased)
                  erased)
               (d_fromℕ'45'mono'45''8804'_3612
                  (coe
                     addInt
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v6 v7 -> v6) v0 v1)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v6 v7 -> v6) v2 v3))
                  (coe
                     addInt
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v6 v7 -> v7) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v6 v7 -> v7) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v2 v3))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804'_3586
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v6 v7 -> v7) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v2 v3)
                     (coe du_m'8804'm'8242'_4232 (coe v0) (coe v1) (coe v4))
                     (coe du_n'8804'n'8242'_4234 (coe v2) (coe v3) (coe v5)))))
            erased)
         erased)
-- Data.Nat.Binary.Properties._.m
d_m_4224 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_m_4224 v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_m_4224 v0
du_m_4224 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_4224 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.m′
d_m'8242'_4226 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_m'8242'_4226 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_m'8242'_4226 v1
du_m'8242'_4226 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m'8242'_4226 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n
d_n_4228 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_n_4228 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_n_4228 v2
du_n_4228 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_4228 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n′
d_n'8242'_4230 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_n'8242'_4230 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_n'8242'_4230 v3
du_n'8242'_4230 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n'8242'_4230 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.m≤m′
d_m'8804'm'8242'_4232 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'm'8242'_4232 v0 v1 ~v2 ~v3 v4 ~v5
  = du_m'8804'm'8242'_4232 v0 v1 v4
du_m'8804'm'8242'_4232 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'm'8242'_4232 v0 v1 v2
  = coe d_toℕ'45'mono'45''8804'_3628 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties._.n≤n′
d_n'8804'n'8242'_4234 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'n'8242'_4234 ~v0 ~v1 v2 v3 ~v4 v5
  = du_n'8804'n'8242'_4234 v2 v3 v5
du_n'8804'n'8242'_4234 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8804'n'8242'_4234 v0 v1 v2
  = coe d_toℕ'45'mono'45''8804'_3628 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties.+-monoˡ-≤
d_'43''45'mono'737''45''8804'_4240 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'43''45'mono'737''45''8804'_4240 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''8804'_4206 (coe v1) (coe v2) (coe v0) (coe v0)
      (coe v3) (coe du_'8804''45'refl_3648)
-- Data.Nat.Binary.Properties.+-monoʳ-≤
d_'43''45'mono'691''45''8804'_4250 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'43''45'mono'691''45''8804'_4250 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''8804'_4206 (coe v0) (coe v0) (coe v1) (coe v2)
      (coe du_'8804''45'refl_3648) (coe v3)
-- Data.Nat.Binary.Properties.+-mono-<-≤
d_'43''45'mono'45''60''45''8804'_4256 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'43''45'mono'45''60''45''8804'_4256 v0 v1 v2 v3 ~v4 ~v5
  = du_'43''45'mono'45''60''45''8804'_4256 v0 v1 v2 v3
du_'43''45'mono'45''60''45''8804'_4256 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'43''45'mono'45''60''45''8804'_4256 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v4)
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v2))
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v5 v6 v7 v8 v9 -> v9)
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v2))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe du_m_4274 (coe v0)))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe du_n_4276 (coe v2))))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v5 v6 v7 v8 v9 -> v9)
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe du_m_4274 (coe v0)))
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe du_n_4276 (coe v2))))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe addInt (coe du_n_4276 (coe v2)) (coe du_m_4274 (coe v0))))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe d_'60''45'trans_3260)
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                     (coe d_'60''45''8804''45'trans_3662))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe addInt (coe du_n_4276 (coe v2)) (coe du_m_4274 (coe v0))))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe
                        addInt (coe du_n'8242'_4280 (coe v3))
                        (coe du_m'8242'_4278 (coe v1))))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v5 v6 v7 v8 v9 -> v9)
                     (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                        (coe
                           addInt (coe du_n'8242'_4280 (coe v3))
                           (coe du_m'8242'_4278 (coe v1))))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                           (coe du_m'8242'_4278 (coe v1)))
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                           (coe du_n'8242'_4280 (coe v3))))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                        (\ v5 v6 v7 v8 v9 -> v9)
                        (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                              (coe du_m'8242'_4278 (coe v1)))
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                              (coe du_n'8242'_4280 (coe v3))))
                        (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
                        (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe d_'8804''45'isPreorder_3742))
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v3)))
                        erased)
                     erased)
                  (coe
                     du_fromℕ'45'mono'45''60'_3248
                     (coe
                        addInt
                        (coe
                           MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                           MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v5 v6 -> v5) v2 v3)
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)))
                     (coe
                        addInt
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                        (coe
                           MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                           (\ v5 v6 -> v6) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v2
                           v3))))
               erased)
            erased))
-- Data.Nat.Binary.Properties._.m
d_m_4274 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_m_4274 v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_m_4274 v0
du_m_4274 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_4274 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n
d_n_4276 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_n_4276 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_n_4276 v2
du_n_4276 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_4276 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.m′
d_m'8242'_4278 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_m'8242'_4278 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_m'8242'_4278 v1
du_m'8242'_4278 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m'8242'_4278 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n′
d_n'8242'_4280 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_n'8242'_4280 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_n'8242'_4280 v3
du_n'8242'_4280 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n'8242'_4280 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.m<m′
d_m'60'm'8242'_4282 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'm'8242'_4282 v0 v1 ~v2 ~v3 v4 ~v5
  = du_m'60'm'8242'_4282 v0 v1 v4
du_m'60'm'8242'_4282 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'm'8242'_4282 v0 v1 v2
  = coe d_toℕ'45'mono'45''60'_3118 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties._.n≤n′
d_n'8804'n'8242'_4284 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'n'8242'_4284 ~v0 ~v1 v2 v3 ~v4 v5
  = du_n'8804'n'8242'_4284 v2 v3 v5
du_n'8804'n'8242'_4284 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8804'n'8242'_4284 v0 v1 v2
  = coe d_toℕ'45'mono'45''8804'_3628 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Binary.Properties.+-mono-≤-<
d_'43''45'mono'45''8804''45''60'_4286 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'43''45'mono'45''8804''45''60'_4286 v0 v1 v2 v3 ~v4 ~v5
  = du_'43''45'mono'45''8804''45''60'_4286 v0 v1 v2 v3
du_'43''45'mono'45''8804''45''60'_4286 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'43''45'mono'45''8804''45''60'_4286 v0 v1 v2 v3
  = coe
      du_y'43'x'60'y'8242''43'x'8242'_4304 (coe v0) (coe v1) (coe v2)
      (coe v3)
-- Data.Nat.Binary.Properties._.y+x<y′+x′
d_y'43'x'60'y'8242''43'x'8242'_4304 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_y'43'x'60'y'8242''43'x'8242'_4304 v0 v1 v2 v3 ~v4 ~v5
  = du_y'43'x'60'y'8242''43'x'8242'_4304 v0 v1 v2 v3
du_y'43'x'60'y'8242''43'x'8242'_4304 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_y'43'x'60'y'8242''43'x'8242'_4304 v0 v1 v2 v3
  = coe
      du_'43''45'mono'45''60''45''8804'_4256 (coe v2) (coe v3) (coe v0)
      (coe v1)
-- Data.Nat.Binary.Properties.+-monoˡ-<
d_'43''45'mono'737''45''60'_4310 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'43''45'mono'737''45''60'_4310 v0 v1 v2 ~v3
  = du_'43''45'mono'737''45''60'_4310 v0 v1 v2
du_'43''45'mono'737''45''60'_4310 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'43''45'mono'737''45''60'_4310 v0 v1 v2
  = coe
      du_'43''45'mono'45''60''45''8804'_4256 (coe v1) (coe v2) (coe v0)
      (coe v0)
-- Data.Nat.Binary.Properties.+-monoʳ-<
d_'43''45'mono'691''45''60'_4320 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'43''45'mono'691''45''60'_4320 v0 v1 v2 ~v3
  = du_'43''45'mono'691''45''60'_4320 v0 v1 v2
du_'43''45'mono'691''45''60'_4320 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'43''45'mono'691''45''60'_4320 v0 v1 v2
  = coe
      du_'43''45'mono'45''8804''45''60'_4286 (coe v0) (coe v0) (coe v1)
      (coe v2)
-- Data.Nat.Binary.Properties.x≤y+x
d_x'8804'y'43'x_4330 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_x'8804'y'43'x_4330 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v2 v3 -> coe du_'60''8658''8804'_3116))
      v0
      (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
         (\ v2 v3 v4 v5 v6 -> v6) v0
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
            (coe MAlonzo.Code.Data.Nat.Binary.Base.d_0'7495'_180) (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_3742)
               (coe d_'8804''45''60''45'trans_3676))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_0'7495'_180) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_3742))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v0)))
            (d_'43''45'mono'737''45''8804'_4240
               (coe v0) (coe MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10) (coe v1)
               (coe d_0'8804'x_3604 (coe v1))))
         erased)
-- Data.Nat.Binary.Properties.x≤x+y
d_x'8804'x'43'y_4344 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_x'8804'x'43'y_4344 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v2 v3 -> coe du_'60''8658''8804'_3116))
      v0
      (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_3742)
            (coe d_'8804''45''60''45'trans_3676))
         v0
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v2 v3 v4 v5 v6 -> v6)
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v1) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_3742))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1)))
            erased)
         (d_x'8804'y'43'x_4330 (coe v0) (coe v1)))
-- Data.Nat.Binary.Properties.x<x+y
d_x'60'x'43'y_4358 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_x'60'x'43'y_4358 v0 v1 ~v2 = du_x'60'x'43'y_4358 v0 v1
du_x'60'x'43'y_4358 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_x'60'x'43'y_4358 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v2) (coe v0)
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v3 v4 v5 v6 v7 -> v7) v0
            (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe d_'60''45'trans_3260)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (coe d_'60''45''8804''45'trans_3662))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe
                     addInt (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1))))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe
                        addInt (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1))))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)))
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1))))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v3 v4 v5 v6 v7 -> v7)
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                           (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)))
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                           (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1))))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_3742))
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v1)))
                     erased)
                  erased)
               (coe
                  du_fromℕ'45'mono'45''60'_3248
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))
                  (coe
                     addInt
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v3 v4 -> v4) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                        MAlonzo.Code.Data.Nat.Binary.Base.d_0'7495'_180 v1)
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)))))
            erased))
-- Data.Nat.Binary.Properties.x<x+1
d_x'60'x'43'1_4372 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_x'60'x'43'1_4372 v0
  = coe
      du_x'60'x'43'y_4358 (coe v0)
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182)
-- Data.Nat.Binary.Properties.x<1+x
d_x'60'1'43'x_4378 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_x'60'1'43'x_4378 v0 = coe d_x'60'x'43'1_4372 (coe v0)
-- Data.Nat.Binary.Properties.x<1⇒x≡0
d_x'60'1'8658'x'8801'0_4386 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'60'1'8658'x'8801'0_4386 = erased
-- Data.Nat.Binary.Properties.x≢0⇒x+y≢0
d_x'8802'0'8658'x'43'y'8802'0_4392 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x'8802'0'8658'x'43'y'8802'0_4392 = erased
-- Data.Nat.Binary.Properties.2*ₙ2*ₙ
d_2'42''8345'2'42''8345'_4396 :: Integer -> Integer
d_2'42''8345'2'42''8345'_4396 v0
  = coe
      mulInt (coe (2 :: Integer))
      (coe mulInt (coe (2 :: Integer)) (coe v0))
-- Data.Nat.Binary.Properties.toℕ-homo-*
d_toℕ'45'homo'45''42'_4406 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'homo'45''42'_4406 = erased
-- Data.Nat.Binary.Properties._.aux
d_aux_4422 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_aux_4422 = erased
-- Data.Nat.Binary.Properties._._.m
d_m_4440 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_m_4440 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_m_4440 v2
du_m_4440 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_4440 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._._.n
d_n_4442 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_n_4442 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_n_4442 v3
du_n_4442 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_4442 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._._.xy
d_xy_4444 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_xy_4444 ~v0 ~v1 v2 v3 ~v4 ~v5 = du_xy_4444 v2 v3
du_xy_4444 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_xy_4444 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v1)
-- Data.Nat.Binary.Properties._._.|x|+|y|≤cnt
d_'124'x'124''43''124'y'124''8804'cnt_4446 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'124'x'124''43''124'y'124''8804'cnt_4446 ~v0 ~v1 v2 v3 ~v4 v5
  = du_'124'x'124''43''124'y'124''8804'cnt_4446 v2 v3 v5
du_'124'x'124''43''124'y'124''8804'cnt_4446 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'124'x'124''43''124'y'124''8804'cnt_4446 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2822
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3598
         (MAlonzo.Code.Data.Nat.Binary.Base.d_size_174 (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_size_174 (coe v1))
         (addInt
            (coe (1 :: Integer))
            (coe MAlonzo.Code.Data.Nat.Binary.Base.d_size_174 (coe v1)))
         (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2902
            (coe MAlonzo.Code.Data.Nat.Binary.Base.d_size_174 (coe v1))))
      (coe v2)
-- Data.Nat.Binary.Properties._._.m
d_m_4470 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_m_4470 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_m_4470 v2
du_m_4470 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_4470 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._._.n
d_n_4472 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_n_4472 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_n_4472 v3
du_n_4472 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_4472 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._._.1+m
d_1'43'm_4474 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_1'43'm_4474 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_1'43'm_4474 v2
du_1'43'm_4474 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_1'43'm_4474 v0
  = coe addInt (coe (1 :: Integer)) (coe du_m_4470 (coe v0))
-- Data.Nat.Binary.Properties._._.2[1+m]
d_2'91'1'43'm'93'_4476 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_2'91'1'43'm'93'_4476 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_2'91'1'43'm'93'_4476 v2
du_2'91'1'43'm'93'_4476 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_2'91'1'43'm'93'_4476 v0
  = coe
      mulInt (coe (2 :: Integer))
      (coe addInt (coe (1 :: Integer)) (coe du_m_4470 (coe v0)))
-- Data.Nat.Binary.Properties._._.eq
d_eq_4478 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_4478 = erased
-- Data.Nat.Binary.Properties._._.|y|+1+|x|≤cnt
d_'124'y'124''43'1'43''124'x'124''8804'cnt_4480 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'124'y'124''43'1'43''124'x'124''8804'cnt_4480 ~v0 ~v1 ~v2 ~v3 ~v4
                                                v5
  = du_'124'y'124''43'1'43''124'x'124''8804'cnt_4480 v5
du_'124'y'124''43'1'43''124'x'124''8804'cnt_4480 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'124'y'124''43'1'43''124'x'124''8804'cnt_4480 v0 = coe v0
-- Data.Nat.Binary.Properties._._.m
d_m_4506 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_m_4506 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_m_4506 v2
du_m_4506 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_4506 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._._.n
d_n_4508 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_n_4508 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_n_4508 v3
du_n_4508 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_4508 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._._.1+n
d_1'43'n_4510 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_1'43'n_4510 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_1'43'n_4510 v3
du_1'43'n_4510 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_1'43'n_4510 v0
  = coe addInt (coe (1 :: Integer)) (coe du_n_4508 (coe v0))
-- Data.Nat.Binary.Properties._._.2m
d_2m_4512 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_2m_4512 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_2m_4512 v2
du_2m_4512 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_2m_4512 v0
  = coe mulInt (coe (2 :: Integer)) (coe du_m_4506 (coe v0))
-- Data.Nat.Binary.Properties._._.2[1+n]
d_2'91'1'43'n'93'_4514 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_2'91'1'43'n'93'_4514 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_2'91'1'43'n'93'_4514 v3
du_2'91'1'43'n'93'_4514 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_2'91'1'43'n'93'_4514 v0
  = coe
      mulInt (coe (2 :: Integer))
      (coe addInt (coe (1 :: Integer)) (coe du_n_4508 (coe v0)))
-- Data.Nat.Binary.Properties._._.m
d_m_4538 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_m_4538 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_m_4538 v2
du_m_4538 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_4538 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._._.n
d_n_4540 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_n_4540 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_n_4540 v3
du_n_4540 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_4540 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._._.2m
d_2m_4542 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_2m_4542 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_2m_4542 v2
du_2m_4542 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_2m_4542 v0
  = coe mulInt (coe (2 :: Integer)) (coe du_m_4538 (coe v0))
-- Data.Nat.Binary.Properties._._.2n
d_2n_4544 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_2n_4544 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_2n_4544 v3
du_2n_4544 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_2n_4544 v0
  = coe mulInt (coe (2 :: Integer)) (coe du_n_4540 (coe v0))
-- Data.Nat.Binary.Properties._._.1+2x
d_1'43'2x_4546 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_1'43'2x_4546 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_1'43'2x_4546 v2
du_1'43'2x_4546 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_1'43'2x_4546 v0
  = coe
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 (coe v0)
-- Data.Nat.Binary.Properties._._.[1+2x]′
d_'91'1'43'2x'93''8242'_4548 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_'91'1'43'2x'93''8242'_4548 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_'91'1'43'2x'93''8242'_4548 v2
du_'91'1'43'2x'93''8242'_4548 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_'91'1'43'2x'93''8242'_4548 v0
  = coe
      MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
      (coe du_1'43'2x_4546 (coe v0))
-- Data.Nat.Binary.Properties._._.eq
d_eq_4550 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_4550 = erased
-- Data.Nat.Binary.Properties._._.|y|+1+|x|≤cnt
d_'124'y'124''43'1'43''124'x'124''8804'cnt_4552 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'124'y'124''43'1'43''124'x'124''8804'cnt_4552 ~v0 ~v1 ~v2 ~v3 ~v4
                                                v5
  = du_'124'y'124''43'1'43''124'x'124''8804'cnt_4552 v5
du_'124'y'124''43'1'43''124'x'124''8804'cnt_4552 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'124'y'124''43'1'43''124'x'124''8804'cnt_4552 v0 = coe v0
-- Data.Nat.Binary.Properties.toℕ-isMagmaHomomorphism-*
d_toℕ'45'isMagmaHomomorphism'45''42'_4566 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_188
d_toℕ'45'isMagmaHomomorphism'45''42'_4566
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMagmaHomomorphism'46'constructor_4629
      (coe d_toℕ'45'isRelHomomorphism_3018) erased
-- Data.Nat.Binary.Properties.toℕ-isMonoidHomomorphism-*
d_toℕ'45'isMonoidHomomorphism'45''42'_4568 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_362
d_toℕ'45'isMonoidHomomorphism'45''42'_4568
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidHomomorphism'46'constructor_9411
      (coe d_toℕ'45'isMagmaHomomorphism'45''42'_4566) erased
-- Data.Nat.Binary.Properties.toℕ-isMonoidMonomorphism-*
d_toℕ'45'isMonoidMonomorphism'45''42'_4570 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384
d_toℕ'45'isMonoidMonomorphism'45''42'_4570
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_IsMonoidMonomorphism'46'constructor_10237
      (coe d_toℕ'45'isMonoidHomomorphism'45''42'_4568) erased
-- Data.Nat.Binary.Properties.fromℕ-homo-*
d_fromℕ'45'homo'45''42'_4576 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'45'homo'45''42'_4576 = erased
-- Data.Nat.Binary.Properties._.a
d_a_4586 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_a_4586 v0 ~v1 = du_a_4586 v0
du_a_4586 ::
  Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_a_4586 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (coe v0)
-- Data.Nat.Binary.Properties._.b
d_b_4588 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_b_4588 ~v0 v1 = du_b_4588 v1
du_b_4588 ::
  Integer -> MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_b_4588 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156 (coe v0)
-- Data.Nat.Binary.Properties._.m≡aN
d_m'8801'aN_4590 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8801'aN_4590 = erased
-- Data.Nat.Binary.Properties._.n≡bN
d_n'8801'bN_4592 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8801'bN_4592 = erased
-- Data.Nat.Binary.Properties.*-assoc
d_'42''45'assoc_4636 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_4636 = erased
-- Data.Nat.Binary.Properties.*-comm
d_'42''45'comm_4638 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_4638 = erased
-- Data.Nat.Binary.Properties.*-identityˡ
d_'42''45'identity'737'_4640 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_4640 = erased
-- Data.Nat.Binary.Properties.*-identityʳ
d_'42''45'identity'691'_4642 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_4642 = erased
-- Data.Nat.Binary.Properties.*-identity
d_'42''45'identity_4646 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_4646
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Binary.Properties.*-zeroˡ
d_'42''45'zero'737'_4648 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'737'_4648 = erased
-- Data.Nat.Binary.Properties.*-zeroʳ
d_'42''45'zero'691'_4650 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'691'_4650 = erased
-- Data.Nat.Binary.Properties.*-zero
d_'42''45'zero_4652 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'zero_4652
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Binary.Properties.*-distribˡ-+
d_'42''45'distrib'737''45''43'_4654 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''43'_4654 = erased
-- Data.Nat.Binary.Properties._.k
d_k_4666 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_k_4666 v0 ~v1 ~v2 = du_k_4666 v0
du_k_4666 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_k_4666 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.m
d_m_4668 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_m_4668 ~v0 v1 ~v2 = du_m_4668 v1
du_m_4668 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_4668 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n
d_n_4670 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
d_n_4670 ~v0 ~v1 v2 = du_n_4670 v2
du_n_4670 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_4670 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties.*-distribʳ-+
d_'42''45'distrib'691''45''43'_4674 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''43'_4674 = erased
-- Data.Nat.Binary.Properties.*-distrib-+
d_'42''45'distrib'45''43'_4676 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''43'_4676
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Binary.Properties.*-isMagma
d_'42''45'isMagma_4678 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_4678
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra.du_isMagma_14
-- Data.Nat.Binary.Properties.*-isSemigroup
d_'42''45'isSemigroup_4680 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_4680
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSemigroup_268
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d_'42''45'1'45'rawMonoid_206))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
         (coe MAlonzo.Code.Data.Nat.Base.d_'42''45'1'45'rawMonoid_186))
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe d_toℕ'45'isMonoidMonomorphism'45''42'_4570))
      (coe MAlonzo.Code.Data.Nat.Properties.d_'42''45'isSemigroup_3778)
-- Data.Nat.Binary.Properties.*-1-isMonoid
d_'42''45'1'45'isMonoid_4682 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'1'45'isMonoid_4682
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isMonoid_192
      (coe
         MAlonzo.Code.Data.Nat.Binary.Base.d_'42''45'1'45'rawMonoid_206)
      (coe MAlonzo.Code.Data.Nat.Base.d_'42''45'1'45'rawMonoid_186)
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150)
      (coe d_toℕ'45'isMonoidMonomorphism'45''42'_4570)
      (coe MAlonzo.Code.Data.Nat.Properties.d_'42''45'1'45'isMonoid_3782)
-- Data.Nat.Binary.Properties.*-1-isCommutativeMonoid
d_'42''45'1'45'isCommutativeMonoid_4684 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'1'45'isCommutativeMonoid_4684
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isCommutativeMonoid_236
      (coe
         MAlonzo.Code.Data.Nat.Binary.Base.d_'42''45'1'45'rawMonoid_206)
      (coe MAlonzo.Code.Data.Nat.Base.d_'42''45'1'45'rawMonoid_186)
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150)
      (coe d_toℕ'45'isMonoidMonomorphism'45''42'_4570)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'42''45'1'45'isCommutativeMonoid_3784)
-- Data.Nat.Binary.Properties.+-*-isSemiringWithoutAnnihilatingZero
d_'43''45''42''45'isSemiringWithoutAnnihilatingZero_4686 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_'43''45''42''45'isSemiringWithoutAnnihilatingZero_4686
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_44883
      (coe d_'43''45'0'45'isCommutativeMonoid_4094) erased erased
      (coe d_'42''45'identity_4646) (coe d_'42''45'distrib'45''43'_4676)
-- Data.Nat.Binary.Properties.+-*-isSemiring
d_'43''45''42''45'isSemiring_4688 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_'43''45''42''45'isSemiring_4688
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_49143
      (coe d_'43''45''42''45'isSemiringWithoutAnnihilatingZero_4686)
      (coe d_'42''45'zero_4652)
-- Data.Nat.Binary.Properties.+-*-isCommutativeSemiring
d_'43''45''42''45'isCommutativeSemiring_4690 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_'43''45''42''45'isCommutativeSemiring_4690
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_52967
      (coe d_'43''45''42''45'isSemiring_4688) erased
-- Data.Nat.Binary.Properties.*-magma
d_'42''45'magma_4692 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'42''45'magma_4692
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1323
      MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
      d_'42''45'isMagma_4678
-- Data.Nat.Binary.Properties.*-semigroup
d_'42''45'semigroup_4694 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'42''45'semigroup_4694
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9837
      MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
      d_'42''45'isSemigroup_4680
-- Data.Nat.Binary.Properties.*-1-monoid
d_'42''45'1'45'monoid_4696 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'42''45'1'45'monoid_4696
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16201
      MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
      MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182
      d_'42''45'1'45'isMonoid_4682
-- Data.Nat.Binary.Properties.*-1-commutativeMonoid
d_'42''45'1'45'commutativeMonoid_4698 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'42''45'1'45'commutativeMonoid_4698
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
      MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182
      d_'42''45'1'45'isCommutativeMonoid_4684
-- Data.Nat.Binary.Properties.+-*-semiring
d_'43''45''42''45'semiring_4700 ::
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
d_'43''45''42''45'semiring_4700
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semiring'46'constructor_42213
      MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
      MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
      (coe MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10)
      MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182
      d_'43''45''42''45'isSemiring_4688
-- Data.Nat.Binary.Properties.+-*-commutativeSemiring
d_'43''45''42''45'commutativeSemiring_4702 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
d_'43''45''42''45'commutativeSemiring_4702
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_45179
      MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
      MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
      (coe MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10)
      MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182
      d_'43''45''42''45'isCommutativeSemiring_4690
-- Data.Nat.Binary.Properties.*-mono-≤
d_'42''45'mono'45''8804'_4704 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'42''45'mono'45''8804'_4704 v0 v1 v2 v3 v4 v5
  = coe
      d_toℕ'45'cancel'45''8804'_3636
      (coe
         MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864)
            (\ v6 v7 v8 ->
               coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2912 v8))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2)))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v3)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v6 v7 v8 v9 v10 -> v10)
            (MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2)))
            (mulInt
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v2)))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864)
                  (\ v6 v7 v8 v9 v10 ->
                     coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3042 v9
                       v10))
               (mulInt
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v2)))
               (mulInt
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1))
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v3)))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v3)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v6 v7 v8 v9 v10 -> v10)
                  (mulInt
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1))
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v3)))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v3)))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v3)))
                  (let v6
                         = MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2864 in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe v6))
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1)
                              (coe v3)))))
                  erased)
               (coe
                  MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'45''8804'_4128
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v6 v7 -> v7) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v3))
                  (coe d_toℕ'45'mono'45''8804'_3628 (coe v0) (coe v1) (coe v4))
                  (coe d_toℕ'45'mono'45''8804'_3628 (coe v2) (coe v3) (coe v5))))
            erased))
-- Data.Nat.Binary.Properties.*-monoʳ-≤
d_'42''45'mono'691''45''8804'_4726 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'42''45'mono'691''45''8804'_4726 v0 v1 v2 v3
  = coe
      d_'42''45'mono'45''8804'_4704 (coe v0) (coe v0) (coe v1) (coe v2)
      (coe du_'8804''45'refl_3648) (coe v3)
-- Data.Nat.Binary.Properties.*-monoˡ-≤
d_'42''45'mono'737''45''8804'_4736 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'42''45'mono'737''45''8804'_4736 v0 v1 v2 v3
  = coe
      d_'42''45'mono'45''8804'_4704 (coe v1) (coe v2) (coe v0) (coe v0)
      (coe v3) (coe du_'8804''45'refl_3648)
-- Data.Nat.Binary.Properties.*-mono-<
d_'42''45'mono'45''60'_4742 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'42''45'mono'45''60'_4742 v0 v1 v2 v3 ~v4 ~v5
  = du_'42''45'mono'45''60'_4742 v0 v1 v2 v3
du_'42''45'mono'45''60'_4742 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'42''45'mono'45''60'_4742 v0 v1 v2 v3
  = coe
      du_toℕ'45'cancel'45''60'_3180
      (coe
         MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v3))
-- Data.Nat.Binary.Properties.*-monoʳ-<
d_'42''45'mono'691''45''60'_4764 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'42''45'mono'691''45''60'_4764 v0 v1 v2 ~v3
  = du_'42''45'mono'691''45''60'_4764 v0 v1 v2
du_'42''45'mono'691''45''60'_4764 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'42''45'mono'691''45''60'_4764 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v3)
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
            (coe v1))
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
            (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v4 v5 v6 v7 v8 -> v8)
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
               (coe v1))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v1))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v1)))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
               (coe v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v4 v5 v6 v7 v8 -> v8)
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v1))
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v1)))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe v1)
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v1)))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                  (coe v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe d_'60''45'trans_3260)
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                     (coe d_'60''45''8804''45'trans_3662))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                     (coe v1)
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v1)))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                     (coe v2)
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2)))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                     (coe v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v4 v5 v6 v7 v8 -> v8)
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe v2)
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2)))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                           (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v2))
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2)))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                           (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                        (coe v2))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                        (\ v4 v5 v6 v7 v8 -> v8)
                        (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                              (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v2))
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2)))
                        (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                              (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                           (coe v2))
                        (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                              (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                           (coe v2))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe d_'8804''45'isPreorder_3742))
                           (coe
                              MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                              (coe
                                 MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                                 (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                              (coe v2)))
                        erased)
                     erased)
                  (coe
                     du_'43''45'mono'45''60''45''8804'_4256 (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v1))
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v0) (coe v2))))
               erased)
            erased))
-- Data.Nat.Binary.Properties.*-monoˡ-<
d_'42''45'mono'737''45''60'_4786 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_'42''45'mono'737''45''60'_4786 v0 v1 v2 ~v3
  = du_'42''45'mono'737''45''60'_4786 v0 v1 v2
du_'42''45'mono'737''45''60'_4786 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_'42''45'mono'737''45''60'_4786 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v3)
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1)
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)))
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v2)
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v4 v5 v6 v7 v8 -> v8)
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe v1)
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
               (coe v1))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe v2)
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe d_'60''45'trans_3260)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (coe d_'60''45''8804''45'trans_3662))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                  (coe v1))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                  (coe v2))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe v2)
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v4 v5 v6 v7 v8 -> v8)
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
                     (coe v2))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                     (coe v2)
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                     (coe v2)
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_3742))
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v2)
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                           (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))))
                  erased)
               (coe du_'42''45'mono'691''45''60'_4764 (coe v0) (coe v1) (coe v2)))
            erased))
-- Data.Nat.Binary.Properties.x*y≡0⇒x≡0∨y≡0
d_x'42'y'8801'0'8658'x'8801'0'8744'y'8801'0_4804 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_x'42'y'8801'0'8658'x'8801'0'8744'y'8801'0_4804 v0 v1 ~v2
  = du_x'42'y'8801'0'8658'x'8801'0'8744'y'8801'0_4804 v0 v1
du_x'42'y'8801'0'8658'x'8801'0'8744'y'8801'0_4804 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_x'42'y'8801'0'8658'x'8801'0'8744'y'8801'0_4804 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 v2
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
      MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 v2
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.x≢0∧y≢0⇒x*y≢0
d_x'8802'0'8743'y'8802'0'8658'x'42'y'8802'0_4810 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x'8802'0'8743'y'8802'0'8658'x'42'y'8802'0_4810 = erased
-- Data.Nat.Binary.Properties.2*x≡x+x
d_2'42'x'8801'x'43'x_4846 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'42'x'8801'x'43'x_4846 = erased
-- Data.Nat.Binary.Properties.1+-*
d_1'43''45''42'_4858 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'43''45''42'_4858 = erased
-- Data.Nat.Binary.Properties.*-1+
d_'42''45'1'43'_4874 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'1'43'_4874 = erased
-- Data.Nat.Binary.Properties.double[x]≡0⇒x≡0
d_double'91'x'93''8801'0'8658'x'8801'0_4886 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'91'x'93''8801'0'8658'x'8801'0_4886 = erased
-- Data.Nat.Binary.Properties.x≡0⇒double[x]≡0
d_x'8801'0'8658'double'91'x'93''8801'0_4888 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'8801'0'8658'double'91'x'93''8801'0_4888 = erased
-- Data.Nat.Binary.Properties.x≢0⇒double[x]≢0
d_x'8802'0'8658'double'91'x'93''8802'0_4890 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x'8802'0'8658'double'91'x'93''8802'0_4890 = erased
-- Data.Nat.Binary.Properties.double≢1
d_double'8802'1_4894 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_double'8802'1_4894 = erased
-- Data.Nat.Binary.Properties.double≗2*
d_double'8791'2'42'_4898 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'8791'2'42'_4898 = erased
-- Data.Nat.Binary.Properties.double-*-assoc
d_double'45''42''45'assoc_4910 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'45''42''45'assoc_4910 = erased
-- Data.Nat.Binary.Properties.double[x]≡x+x
d_double'91'x'93''8801'x'43'x_4924 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'91'x'93''8801'x'43'x_4924 = erased
-- Data.Nat.Binary.Properties.double-distrib-+
d_double'45'distrib'45''43'_4932 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'45'distrib'45''43'_4932 = erased
-- Data.Nat.Binary.Properties.double-mono-≤
d_double'45'mono'45''8804'_4942 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_double'45'mono'45''8804'_4942 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v3 v4 -> coe du_'60''8658''8804'_3116))
      (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
      (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
         (\ v3 v4 v5 v6 v7 -> v7)
         (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
            (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_3742)
               (coe d_'8804''45''60''45'trans_3676))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v1))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v3 v4 v5 v6 v7 -> v7)
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v1))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3742))
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1)))
               erased)
            (d_'42''45'mono'691''45''8804'_4726
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v0)
               (coe v1) (coe v2)))
         erased)
-- Data.Nat.Binary.Properties.double-mono-<
d_double'45'mono'45''60'_4954 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_double'45'mono'45''60'_4954 v0 v1 ~v2
  = du_double'45'mono'45''60'_4954 v0 v1
du_double'45'mono'45''60'_4954 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_double'45'mono'45''60'_4954 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v2)
         (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
         (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v3 v4 v5 v6 v7 -> v7)
            (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe d_'60''45'trans_3260)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (coe d_'60''45''8804''45'trans_3662))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v0))
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v1))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_2'7495'_184) (coe v1))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_3742))
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v1)))
                  erased)
               (coe
                  du_'42''45'mono'691''45''60'_4764
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)
                  (coe v1)))
            erased))
-- Data.Nat.Binary.Properties.double-cancel-≤
d_double'45'cancel'45''8804'_4970 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_double'45'cancel'45''8804'_4970 v0 v1 ~v2
  = du_double'45'cancel'45''8804'_4970 v0 v1
du_double'45'cancel'45''8804'_4970 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_double'45'cancel'45''8804'_4970 v0 v1
  = let v2 = d_'60''45'cmp_3308 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v3
           -> coe du_'60''8658''8804'_3116 v3
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v4
           -> coe du_'8804''45'reflexive_3650
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v5
           -> coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Binary.Properties.double-cancel-<
d_double'45'cancel'45''60'_5010 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_double'45'cancel'45''60'_5010 v0 v1 ~v2
  = du_double'45'cancel'45''60'_5010 v0 v1
du_double'45'cancel'45''60'_5010 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_double'45'cancel'45''60'_5010 v0 v1
  = let v2 = d_'60''45'cmp_3308 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v3 -> coe v3
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v4
           -> coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v5
           -> coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Binary.Properties.x<double[x]
d_x'60'double'91'x'93'_5046 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_x'60'double'91'x'93'_5046 v0 ~v1
  = du_x'60'double'91'x'93'_5046 v0
du_x'60'double'91'x'93'_5046 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_x'60'double'91'x'93'_5046 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v1) (coe v0)
         (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (coe d_'60''45'trans_3260)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (coe d_'60''45''8804''45'trans_3662))
            v0
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v0))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3742))
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0)))
               erased)
            (coe du_x'60'x'43'y_4358 (coe v0) (coe v0))))
-- Data.Nat.Binary.Properties.x≤double[x]
d_x'8804'double'91'x'93'_5058 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_x'8804'double'91'x'93'_5058 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v1 v2 -> coe du_'60''8658''8804'_3116))
      v0 (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_3742)
            (coe d_'8804''45''60''45'trans_3676))
         v0
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v1 v2 v3 v4 v5 -> v5)
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110 (coe v0) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_3742))
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0)))
            erased)
         (d_x'8804'x'43'y_4344 (coe v0) (coe v0)))
-- Data.Nat.Binary.Properties.double-suc
d_double'45'suc_5068 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_double'45'suc_5068 = erased
-- Data.Nat.Binary.Properties.suc≢0
d_suc'8802'0_5076 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_suc'8802'0_5076 = erased
-- Data.Nat.Binary.Properties.suc-injective
d_suc'45'injective_5078 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'injective_5078 = erased
-- Data.Nat.Binary.Properties.2[1+_]-double-suc
d_2'91'1'43'_'93''45'double'45'suc_5100 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_2'91'1'43'_'93''45'double'45'suc_5100 = erased
-- Data.Nat.Binary.Properties.1+[2_]-suc-double
d_1'43''91'2_'93''45'suc'45'double_5106 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'43''91'2_'93''45'suc'45'double_5106 = erased
-- Data.Nat.Binary.Properties._.2x
d_2x_5116 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_2x_5116 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0)
-- Data.Nat.Binary.Properties.x+suc[y]≡suc[x]+y
d_x'43'suc'91'y'93''8801'suc'91'x'93''43'y_5122 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x'43'suc'91'y'93''8801'suc'91'x'93''43'y_5122 = erased
-- Data.Nat.Binary.Properties.0<suc
d_0'60'suc_5134 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_0'60'suc_5134 v0
  = coe
      du_x'8802'0'8658'x'62'0_3058
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
-- Data.Nat.Binary.Properties.x<suc[x]
d_x'60'suc'91'x'93'_5140 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_x'60'suc'91'x'93'_5140 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v1) (coe v0)
         (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (coe d_'60''45'trans_3260)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (coe d_'60''45''8804''45'trans_3662))
            v0
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3742))
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0)))
               erased)
            (d_x'60'1'43'x_4378 (coe v0))))
-- Data.Nat.Binary.Properties.x≤suc[x]
d_x'8804'suc'91'x'93'_5150 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_x'8804'suc'91'x'93'_5150 v0
  = coe du_'60''8658''8804'_3116 (d_x'60'suc'91'x'93'_5140 (coe v0))
-- Data.Nat.Binary.Properties.x≢suc[x]
d_x'8802'suc'91'x'93'_5156 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x'8802'suc'91'x'93'_5156 = erased
-- Data.Nat.Binary.Properties.suc-mono-≤
d_suc'45'mono'45''8804'_5160 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_suc'45'mono'45''8804'_5160 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v3 v4 -> coe du_'60''8658''8804'_3116))
      (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
      (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
         (\ v3 v4 v5 v6 v7 -> v7)
         (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
            (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_3742)
               (coe d_'8804''45''60''45'trans_3676))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v1))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v3 v4 v5 v6 v7 -> v7)
               (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v1))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3742))
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1)))
               erased)
            (d_'43''45'mono'691''45''8804'_4250
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_1'7495'_182) (coe v0)
               (coe v1) (coe v2)))
         erased)
-- Data.Nat.Binary.Properties.suc[x]≤y⇒x<y
d_suc'91'x'93''8804'y'8658'x'60'y_5176 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_suc'91'x'93''8804'y'8658'x'60'y_5176 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> coe
             d_'60''45'trans_3260 (coe v0)
             (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0)) (coe v1)
             (coe d_x'60'suc'91'x'93'_5140 (coe v0)) (coe v3)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe d_x'60'suc'91'x'93'_5140 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Properties.x<y⇒suc[x]≤y
d_x'60'y'8658'suc'91'x'93''8804'y_5188 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_x'60'y'8658'suc'91'x'93''8804'y_5188 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v3 v4 -> coe du_'60''8658''8804'_3116))
      (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0)) v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
         (\ v3 v4 v5 v6 v7 -> v7)
         (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v3 v4 v5 v6 v7 -> v7)
            (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe
                  addInt (coe (1 :: Integer))
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe d_'8804''45'isPreorder_3742)
                  (coe d_'8804''45''60''45'trans_3676))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe
                     addInt (coe (1 :: Integer))
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0))))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1)))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v1)))
                  v1 v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_3742))
                     (coe v1))
                  erased)
               (d_fromℕ'45'mono'45''8804'_3612
                  (coe
                     addInt (coe (1 :: Integer))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v3 v4 -> v3) v0 v1))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v3 v4 -> v4) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1)
                  (coe d_toℕ'45'mono'45''60'_3118 (coe v0) (coe v1) (coe v2))))
            erased)
         erased)
-- Data.Nat.Binary.Properties.suc-*
d_suc'45''42'_5204 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45''42'_5204 = erased
-- Data.Nat.Binary.Properties.*-suc
d_'42''45'suc_5220 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'suc_5220 = erased
-- Data.Nat.Binary.Properties.x≤suc[y]*x
d_x'8804'suc'91'y'93''42'x_5236 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_x'8804'suc'91'y'93''42'x_5236 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v2 v3 -> coe du_'60''8658''8804'_3116))
      v0
      (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
         (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1)) (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_3742)
            (coe d_'8804''45''60''45'trans_3676))
         v0
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
            (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v0)))
         (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
            (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1)) (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v2 v3 v4 v5 v6 -> v6)
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110
               (coe v0)
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v0)))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1)) (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1)) (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_3742))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v1))
                  (coe v0)))
            erased)
         (d_x'8804'x'43'y_4344
            (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d__'42'__132 (coe v1) (coe v0))))
-- Data.Nat.Binary.Properties.suc[x]≤double[x]
d_suc'91'x'93''8804'double'91'x'93'_5248 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_suc'91'x'93''8804'double'91'x'93'_5248 v0 ~v1
  = du_suc'91'x'93''8804'double'91'x'93'_5248 v0
du_suc'91'x'93''8804'double'91'x'93'_5248 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_suc'91'x'93''8804'double'91'x'93'_5248 v0
  = coe
      d_x'60'y'8658'suc'91'x'93''8804'y_5188 (coe v0)
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
      (coe du_x'60'double'91'x'93'_5046 (coe v0))
-- Data.Nat.Binary.Properties.suc[x]<2[1+x]
d_suc'91'x'93''60'2'91'1'43'x'93'_5254 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_suc'91'x'93''60'2'91'1'43'x'93'_5254 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v1) (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (coe d_'60''45'trans_3260)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (coe d_'60''45''8804''45'trans_3662))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0)))
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0)))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 (coe v0))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3742))
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.C_2'91'1'43'_'93'_12 (coe v0)))
               erased)
            (coe
               du_x'60'double'91'x'93'_5046
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98 (coe v0)))))
-- Data.Nat.Binary.Properties.double[x]<1+[2x]
d_double'91'x'93''60'1'43''91'2x'93'_5264 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_double'91'x'93''60'1'43''91'2x'93'_5264 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v1)
         (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
         (coe
            MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (coe d_'60''45'trans_3260)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (coe d_'60''45''8804''45'trans_3662))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0)))
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0)))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 (coe v0))
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3742))
                  (coe
                     MAlonzo.Code.Data.Nat.Binary.Base.C_1'43''91'2_'93'_14 (coe v0)))
               erased)
            (d_x'60'suc'91'x'93'_5140
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_double_92 (coe v0)))))
-- Data.Nat.Binary.Properties.pred-suc
d_pred'45'suc_5272 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'45'suc_5272 = erased
-- Data.Nat.Binary.Properties.suc-pred
d_suc'45'pred_5278 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'pred_5278 = erased
-- Data.Nat.Binary.Properties.pred-mono-≤
d_pred'45'mono'45''8804'_5284 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_pred'45'mono'45''8804'_5284 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_3742)
         (\ v3 v4 -> coe du_'60''8658''8804'_3116))
      (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0))
      (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
         (\ v3 v4 v5 v6 v7 -> v7)
         (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104
            (coe
               MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe du_m_5296 (coe v0))))
         (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v3 v4 v5 v6 v7 -> v7)
            (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104
               (coe
                  MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe du_m_5296 (coe v0))))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
               (coe
                  MAlonzo.Code.Data.Nat.Base.d_pred_192 (coe du_m_5296 (coe v0))))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe d_'8804''45'isPreorder_3742)
                  (coe d_'8804''45''60''45'trans_3676))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d_pred_192 (coe du_m_5296 (coe v0))))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d_pred_192 (coe du_n_5298 (coe v1))))
               (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                     (coe
                        MAlonzo.Code.Data.Nat.Base.d_pred_192 (coe du_n_5298 (coe v1))))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104
                     (coe
                        MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                        (coe du_n_5298 (coe v1))))
                  (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v3 v4 v5 v6 v7 -> v7)
                     (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104
                        (coe
                           MAlonzo.Code.Data.Nat.Binary.Base.d_fromℕ_156
                           (coe du_n_5298 (coe v1))))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v1))
                     (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v1))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_3742))
                        (coe MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v1)))
                     erased)
                  erased)
               (d_fromℕ'45'mono'45''8804'_3612
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     MAlonzo.Code.Data.Nat.Base.d_pred_192 (\ v3 v4 -> v3)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v3 v4 -> v3) v0 v1)
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v3 v4 -> v4) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v3 v4 -> v4) MAlonzo.Code.Data.Nat.Base.d_pred_192
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v3 v4 -> v3) v0 v1)
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v3 v4 -> v4) MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 v0 v1))
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_pred'45'mono'45''8804'_5732
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (\ v3 v4 -> v3) v0 v1)
                     (coe d_toℕ'45'mono'45''8804'_3628 (coe v0) (coe v1) (coe v2)))))
            erased)
         erased)
-- Data.Nat.Binary.Properties._.m
d_m_5296 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_m_5296 v0 ~v1 ~v2 = du_m_5296 v0
du_m_5296 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_m_5296 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties._.n
d_n_5298 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_n_5298 ~v0 v1 ~v2 = du_n_5298 v1
du_n_5298 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 -> Integer
du_n_5298 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_toℕ_150 (coe v0)
-- Data.Nat.Binary.Properties.pred[x]<x
d_pred'91'x'93''60'x_5300 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
d_pred'91'x'93''60'x_5300 v0 ~v1 = du_pred'91'x'93''60'x_5300 v0
du_pred'91'x'93''60'x_5300 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T__'60'__16
du_pred'91'x'93''60'x_5300 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v1)
         (coe MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0))
         (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (coe d_'60''45'trans_3260)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (coe d_'60''45''8804''45'trans_3662))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0))
            (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0)))
            v0
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Nat.Binary.Base.d_suc_98
                  (coe MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0)))
               v0 v0
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_3742))
                  (coe v0))
               erased)
            (d_x'60'suc'91'x'93'_5140
               (coe MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0)))))
-- Data.Nat.Binary.Properties.pred[x]+y≡x+pred[y]
d_pred'91'x'93''43'y'8801'x'43'pred'91'y'93'_5314 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'91'x'93''43'y'8801'x'43'pred'91'y'93'_5314 = erased
-- Data.Nat.Binary.Properties._.px
d_px_5328 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_px_5328 v0 ~v1 ~v2 ~v3 = du_px_5328 v0
du_px_5328 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_px_5328 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0)
-- Data.Nat.Binary.Properties._.py
d_py_5330 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
d_py_5330 ~v0 v1 ~v2 ~v3 = du_py_5330 v1
du_py_5330 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8
du_py_5330 v0
  = coe MAlonzo.Code.Data.Nat.Binary.Base.d_pred_104 (coe v0)
-- Data.Nat.Binary.Properties.|x|≡0⇒x≡0
d_'124'x'124''8801'0'8658'x'8801'0_5340 ::
  MAlonzo.Code.Data.Nat.Binary.Base.T_ℕ'7495'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'124'x'124''8801'0'8658'x'8801'0_5340 = erased
-- Data.Nat.Binary.Properties.*-+-isSemiringWithoutAnnihilatingZero
d_'42''45''43''45'isSemiringWithoutAnnihilatingZero_5342 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_'42''45''43''45'isSemiringWithoutAnnihilatingZero_5342
  = coe d_'43''45''42''45'isSemiringWithoutAnnihilatingZero_4686
-- Data.Nat.Binary.Properties.*-+-isSemiring
d_'42''45''43''45'isSemiring_5344 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_'42''45''43''45'isSemiring_5344
  = coe d_'43''45''42''45'isSemiring_4688
-- Data.Nat.Binary.Properties.*-+-isCommutativeSemiring
d_'42''45''43''45'isCommutativeSemiring_5346 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_'42''45''43''45'isCommutativeSemiring_5346
  = coe d_'43''45''42''45'isCommutativeSemiring_4690
-- Data.Nat.Binary.Properties.*-+-semiring
d_'42''45''43''45'semiring_5348 ::
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2304
d_'42''45''43''45'semiring_5348
  = coe d_'43''45''42''45'semiring_4700
-- Data.Nat.Binary.Properties.*-+-commutativeSemiring
d_'42''45''43''45'commutativeSemiring_5350 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2470
d_'42''45''43''45'commutativeSemiring_5350
  = coe d_'43''45''42''45'commutativeSemiring_4702
