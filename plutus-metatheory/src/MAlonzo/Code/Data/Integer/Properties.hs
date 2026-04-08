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

module MAlonzo.Code.Data.Integer.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Morphism.Structures
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Integer.Properties._._Absorbs_
d__Absorbs__8 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__Absorbs__8 = erased
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
-- Data.Integer.Properties._._IdempotentOn_
d__IdempotentOn__16 ::
  (Integer -> Integer -> Integer) -> Integer -> ()
d__IdempotentOn__16 = erased
-- Data.Integer.Properties._._MiddleFourExchange_
d__MiddleFourExchange__18 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__MiddleFourExchange__18 = erased
-- Data.Integer.Properties._.Absorptive
d_Absorptive_20 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_Absorptive_20 = erased
-- Data.Integer.Properties._.AlmostCancellative
d_AlmostCancellative_22 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_AlmostCancellative_22 = erased
-- Data.Integer.Properties._.AlmostLeftCancellative
d_AlmostLeftCancellative_24 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_AlmostLeftCancellative_24 = erased
-- Data.Integer.Properties._.AlmostRightCancellative
d_AlmostRightCancellative_26 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_AlmostRightCancellative_26 = erased
-- Data.Integer.Properties._.Alternative
d_Alternative_28 :: (Integer -> Integer -> Integer) -> ()
d_Alternative_28 = erased
-- Data.Integer.Properties._.Associative
d_Associative_30 :: (Integer -> Integer -> Integer) -> ()
d_Associative_30 = erased
-- Data.Integer.Properties._.Cancellative
d_Cancellative_32 :: (Integer -> Integer -> Integer) -> ()
d_Cancellative_32 = erased
-- Data.Integer.Properties._.Commutative
d_Commutative_34 :: (Integer -> Integer -> Integer) -> ()
d_Commutative_34 = erased
-- Data.Integer.Properties._.Congruent₁
d_Congruent'8321'_36 :: (Integer -> Integer) -> ()
d_Congruent'8321'_36 = erased
-- Data.Integer.Properties._.Congruent₂
d_Congruent'8322'_38 :: (Integer -> Integer -> Integer) -> ()
d_Congruent'8322'_38 = erased
-- Data.Integer.Properties._.Conical
d_Conical_40 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Conical_40 = erased
-- Data.Integer.Properties._.Flexible
d_Flexible_42 :: (Integer -> Integer -> Integer) -> ()
d_Flexible_42 = erased
-- Data.Integer.Properties._.Idempotent
d_Idempotent_44 :: (Integer -> Integer -> Integer) -> ()
d_Idempotent_44 = erased
-- Data.Integer.Properties._.IdempotentFun
d_IdempotentFun_46 :: (Integer -> Integer) -> ()
d_IdempotentFun_46 = erased
-- Data.Integer.Properties._.Identical
d_Identical_48 :: (Integer -> Integer -> Integer) -> ()
d_Identical_48 = erased
-- Data.Integer.Properties._.Identity
d_Identity_50 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Identity_50 = erased
-- Data.Integer.Properties._.Interchangable
d_Interchangable_52 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_Interchangable_52 = erased
-- Data.Integer.Properties._.Inverse
d_Inverse_54 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_Inverse_54 = erased
-- Data.Integer.Properties._.Invertible
d_Invertible_56 ::
  Integer -> (Integer -> Integer -> Integer) -> Integer -> ()
d_Invertible_56 = erased
-- Data.Integer.Properties._.Involutive
d_Involutive_58 :: (Integer -> Integer) -> ()
d_Involutive_58 = erased
-- Data.Integer.Properties._.LeftAlternative
d_LeftAlternative_60 :: (Integer -> Integer -> Integer) -> ()
d_LeftAlternative_60 = erased
-- Data.Integer.Properties._.LeftBol
d_LeftBol_62 :: (Integer -> Integer -> Integer) -> ()
d_LeftBol_62 = erased
-- Data.Integer.Properties._.LeftCancellative
d_LeftCancellative_64 :: (Integer -> Integer -> Integer) -> ()
d_LeftCancellative_64 = erased
-- Data.Integer.Properties._.LeftCongruent
d_LeftCongruent_66 :: (Integer -> Integer -> Integer) -> ()
d_LeftCongruent_66 = erased
-- Data.Integer.Properties._.LeftConical
d_LeftConical_68 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftConical_68 = erased
-- Data.Integer.Properties._.LeftDivides
d_LeftDivides_70 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_LeftDivides_70 = erased
-- Data.Integer.Properties._.LeftDividesʳ
d_LeftDivides'691'_72 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_LeftDivides'691'_72 = erased
-- Data.Integer.Properties._.LeftDividesˡ
d_LeftDivides'737'_74 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_LeftDivides'737'_74 = erased
-- Data.Integer.Properties._.LeftIdentity
d_LeftIdentity_76 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftIdentity_76 = erased
-- Data.Integer.Properties._.LeftInverse
d_LeftInverse_78 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_LeftInverse_78 = erased
-- Data.Integer.Properties._.LeftInvertible
d_LeftInvertible_80 ::
  Integer -> (Integer -> Integer -> Integer) -> Integer -> ()
d_LeftInvertible_80 = erased
-- Data.Integer.Properties._.LeftSemimedial
d_LeftSemimedial_82 :: (Integer -> Integer -> Integer) -> ()
d_LeftSemimedial_82 = erased
-- Data.Integer.Properties._.LeftZero
d_LeftZero_84 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftZero_84 = erased
-- Data.Integer.Properties._.Medial
d_Medial_86 :: (Integer -> Integer -> Integer) -> ()
d_Medial_86 = erased
-- Data.Integer.Properties._.MiddleBol
d_MiddleBol_88 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_MiddleBol_88 = erased
-- Data.Integer.Properties._.RightAlternative
d_RightAlternative_90 :: (Integer -> Integer -> Integer) -> ()
d_RightAlternative_90 = erased
-- Data.Integer.Properties._.RightBol
d_RightBol_92 :: (Integer -> Integer -> Integer) -> ()
d_RightBol_92 = erased
-- Data.Integer.Properties._.RightCancellative
d_RightCancellative_94 :: (Integer -> Integer -> Integer) -> ()
d_RightCancellative_94 = erased
-- Data.Integer.Properties._.RightCongruent
d_RightCongruent_96 :: (Integer -> Integer -> Integer) -> ()
d_RightCongruent_96 = erased
-- Data.Integer.Properties._.RightConical
d_RightConical_98 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_RightConical_98 = erased
-- Data.Integer.Properties._.RightDivides
d_RightDivides_100 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_RightDivides_100 = erased
-- Data.Integer.Properties._.RightDividesʳ
d_RightDivides'691'_102 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_RightDivides'691'_102 = erased
-- Data.Integer.Properties._.RightDividesˡ
d_RightDivides'737'_104 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_RightDivides'737'_104 = erased
-- Data.Integer.Properties._.RightIdentity
d_RightIdentity_106 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_RightIdentity_106 = erased
-- Data.Integer.Properties._.RightInverse
d_RightInverse_108 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_RightInverse_108 = erased
-- Data.Integer.Properties._.RightInvertible
d_RightInvertible_110 ::
  Integer -> (Integer -> Integer -> Integer) -> Integer -> ()
d_RightInvertible_110 = erased
-- Data.Integer.Properties._.RightSemimedial
d_RightSemimedial_112 :: (Integer -> Integer -> Integer) -> ()
d_RightSemimedial_112 = erased
-- Data.Integer.Properties._.RightZero
d_RightZero_114 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_RightZero_114 = erased
-- Data.Integer.Properties._.Selective
d_Selective_116 :: (Integer -> Integer -> Integer) -> ()
d_Selective_116 = erased
-- Data.Integer.Properties._.SelfInverse
d_SelfInverse_118 :: (Integer -> Integer) -> ()
d_SelfInverse_118 = erased
-- Data.Integer.Properties._.Semimedial
d_Semimedial_120 :: (Integer -> Integer -> Integer) -> ()
d_Semimedial_120 = erased
-- Data.Integer.Properties._.StarDestructive
d_StarDestructive_122 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarDestructive_122 = erased
-- Data.Integer.Properties._.StarExpansive
d_StarExpansive_124 ::
  Integer ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarExpansive_124 = erased
-- Data.Integer.Properties._.StarLeftDestructive
d_StarLeftDestructive_126 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarLeftDestructive_126 = erased
-- Data.Integer.Properties._.StarLeftExpansive
d_StarLeftExpansive_128 ::
  Integer ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarLeftExpansive_128 = erased
-- Data.Integer.Properties._.StarRightDestructive
d_StarRightDestructive_130 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarRightDestructive_130 = erased
-- Data.Integer.Properties._.StarRightExpansive
d_StarRightExpansive_132 ::
  Integer ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarRightExpansive_132 = erased
-- Data.Integer.Properties._.Zero
d_Zero_134 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Zero_134 = erased
-- Data.Integer.Properties._.IsAbelianGroup
d_IsAbelianGroup_138 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsAlternativeMagma
d_IsAlternativeMagma_142 a0 = ()
-- Data.Integer.Properties._.IsBand
d_IsBand_146 a0 = ()
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_150 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsCommutativeBand
d_IsCommutativeBand_154 a0 = ()
-- Data.Integer.Properties._.IsCommutativeMagma
d_IsCommutativeMagma_158 a0 = ()
-- Data.Integer.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_162 a0 a1 = ()
-- Data.Integer.Properties._.IsCommutativeRing
d_IsCommutativeRing_166 a0 a1 a2 a3 a4 = ()
-- Data.Integer.Properties._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_170 a0 = ()
-- Data.Integer.Properties._.IsCommutativeSemiring
d_IsCommutativeSemiring_174 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_178 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsFlexibleMagma
d_IsFlexibleMagma_182 a0 = ()
-- Data.Integer.Properties._.IsGroup
d_IsGroup_186 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_190 a0 a1 = ()
-- Data.Integer.Properties._.IsIdempotentMagma
d_IsIdempotentMagma_194 a0 = ()
-- Data.Integer.Properties._.IsIdempotentMonoid
d_IsIdempotentMonoid_198 a0 a1 = ()
-- Data.Integer.Properties._.IsIdempotentSemiring
d_IsIdempotentSemiring_202 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsInvertibleMagma
d_IsInvertibleMagma_206 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_210 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsKleeneAlgebra
d_IsKleeneAlgebra_214 a0 a1 a2 a3 a4 = ()
-- Data.Integer.Properties._.IsLeftBolLoop
d_IsLeftBolLoop_218 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsLoop
d_IsLoop_222 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsMagma
d_IsMagma_226 a0 = ()
-- Data.Integer.Properties._.IsMedialMagma
d_IsMedialMagma_230 a0 = ()
-- Data.Integer.Properties._.IsMiddleBolLoop
d_IsMiddleBolLoop_234 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsMonoid
d_IsMonoid_238 a0 a1 = ()
-- Data.Integer.Properties._.IsMoufangLoop
d_IsMoufangLoop_242 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsNearSemiring
d_IsNearSemiring_246 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsNearring
d_IsNearring_250 a0 a1 a2 a3 a4 = ()
-- Data.Integer.Properties._.IsNonAssociativeRing
d_IsNonAssociativeRing_254 a0 a1 a2 a3 a4 = ()
-- Data.Integer.Properties._.IsQuasigroup
d_IsQuasigroup_258 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsQuasiring
d_IsQuasiring_262 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsRightBolLoop
d_IsRightBolLoop_266 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsRing
d_IsRing_270 a0 a1 a2 a3 a4 = ()
-- Data.Integer.Properties._.IsRingWithoutOne
d_IsRingWithoutOne_274 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsSelectiveMagma
d_IsSelectiveMagma_278 a0 = ()
-- Data.Integer.Properties._.IsSemigroup
d_IsSemigroup_282 a0 = ()
-- Data.Integer.Properties._.IsSemimedialMagma
d_IsSemimedialMagma_286 a0 = ()
-- Data.Integer.Properties._.IsSemiring
d_IsSemiring_290 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_294 a0 a1 a2 a3 = ()
-- Data.Integer.Properties._.IsSemiringWithoutOne
d_IsSemiringWithoutOne_298 a0 a1 a2 = ()
-- Data.Integer.Properties._.IsSuccessorSet
d_IsSuccessorSet_302 a0 a1 = ()
-- Data.Integer.Properties._.IsUnitalMagma
d_IsUnitalMagma_306 a0 a1 = ()
-- Data.Integer.Properties._.IsAbelianGroup._//_
d__'47''47'__312 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> Integer -> Integer
d__'47''47'__312 v0 ~v1 v2 ~v3 = du__'47''47'__312 v0 v2
du__'47''47'__312 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__312 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Integer.Properties._.IsAbelianGroup.assoc
d_assoc_314 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_314 = erased
-- Data.Integer.Properties._.IsAbelianGroup.comm
d_comm_316 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_316 = erased
-- Data.Integer.Properties._.IsAbelianGroup.identity
d_identity_318 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_318 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))
-- Data.Integer.Properties._.IsAbelianGroup.identityʳ
d_identity'691'_320 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_320 = erased
-- Data.Integer.Properties._.IsAbelianGroup.identityˡ
d_identity'737'_322 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_322 = erased
-- Data.Integer.Properties._.IsAbelianGroup.inverse
d_inverse_324 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Integer.Properties._.IsAbelianGroup.inverseʳ
d_inverse'691'_326 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_326 = erased
-- Data.Integer.Properties._.IsAbelianGroup.inverseˡ
d_inverse'737'_328 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_328 = erased
-- Data.Integer.Properties._.IsAbelianGroup.isCommutativeMagma
d_isCommutativeMagma_330 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_330 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_330 v3
du_isCommutativeMagma_330 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_330 v0
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
-- Data.Integer.Properties._.IsAbelianGroup.isCommutativeMonoid
d_isCommutativeMonoid_332 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_332 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244 v3
-- Data.Integer.Properties._.IsAbelianGroup.isCommutativeSemigroup
d_isCommutativeSemigroup_334 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_334 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_334 v3
du_isCommutativeSemigroup_334 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_334 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
         (coe v0))
-- Data.Integer.Properties._.IsAbelianGroup.isEquivalence
d_isEquivalence_336 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_336 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))))
-- Data.Integer.Properties._.IsAbelianGroup.isGroup
d_isGroup_338 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_338 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)
-- Data.Integer.Properties._.IsAbelianGroup.isInvertibleMagma
d_isInvertibleMagma_340 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_340 ~v0 ~v1 ~v2 v3
  = du_isInvertibleMagma_340 v3
du_isInvertibleMagma_340 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_340 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Integer.Properties._.IsAbelianGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_342 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_342 ~v0 ~v1 ~v2 v3
  = du_isInvertibleUnitalMagma_342 v3
du_isInvertibleUnitalMagma_342 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_342 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Integer.Properties._.IsAbelianGroup.isMagma
d_isMagma_344 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_344 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))))
-- Data.Integer.Properties._.IsAbelianGroup.isMonoid
d_isMonoid_346 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_346 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Integer.Properties._.IsAbelianGroup.isPartialEquivalence
d_isPartialEquivalence_348 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_348 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_348 v3
du_isPartialEquivalence_348 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_348 v0
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
-- Data.Integer.Properties._.IsAbelianGroup.isSemigroup
d_isSemigroup_350 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_350 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))
-- Data.Integer.Properties._.IsAbelianGroup.isUnitalMagma
d_isUnitalMagma_352 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_352 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_352 v3
du_isUnitalMagma_352 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_352 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1)))
-- Data.Integer.Properties._.IsAbelianGroup.refl
d_refl_354 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_354 = erased
-- Data.Integer.Properties._.IsAbelianGroup.reflexive
d_reflexive_356 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_356 = erased
-- Data.Integer.Properties._.IsAbelianGroup.setoid
d_setoid_358 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_358 ~v0 ~v1 ~v2 v3 = du_setoid_358 v3
du_setoid_358 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_358 v0
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
-- Data.Integer.Properties._.IsAbelianGroup.sym
d_sym_360 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_360 = erased
-- Data.Integer.Properties._.IsAbelianGroup.trans
d_trans_362 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_362 = erased
-- Data.Integer.Properties._.IsAbelianGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_364 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_364 = erased
-- Data.Integer.Properties._.IsAbelianGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_366 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_366 = erased
-- Data.Integer.Properties._.IsAbelianGroup.⁻¹-cong
d_'8315''185''45'cong_368 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_368 = erased
-- Data.Integer.Properties._.IsAbelianGroup.∙-cong
d_'8729''45'cong_370 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_370 = erased
-- Data.Integer.Properties._.IsAbelianGroup.∙-congʳ
d_'8729''45'cong'691'_372 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_372 = erased
-- Data.Integer.Properties._.IsAbelianGroup.∙-congˡ
d_'8729''45'cong'737'_374 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_374 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.alter
d_alter_378 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_378 v0
  = coe MAlonzo.Code.Algebra.Structures.d_alter_300 (coe v0)
-- Data.Integer.Properties._.IsAlternativeMagma.alternativeʳ
d_alternative'691'_380 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'691'_380 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.alternativeˡ
d_alternative'737'_382 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'737'_382 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.isEquivalence
d_isEquivalence_384 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_384 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0))
-- Data.Integer.Properties._.IsAlternativeMagma.isMagma
d_isMagma_386 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_386 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0)
-- Data.Integer.Properties._.IsAlternativeMagma.isPartialEquivalence
d_isPartialEquivalence_388 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_388 ~v0 v1 = du_isPartialEquivalence_388 v1
du_isPartialEquivalence_388 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_388 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsAlternativeMagma.refl
d_refl_390 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_390 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.reflexive
d_reflexive_392 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_392 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.setoid
d_setoid_394 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_394 ~v0 v1 = du_setoid_394 v1
du_setoid_394 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_394 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0))
-- Data.Integer.Properties._.IsAlternativeMagma.sym
d_sym_396 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_396 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.trans
d_trans_398 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_398 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.∙-cong
d_'8729''45'cong_400 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_400 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.∙-congʳ
d_'8729''45'cong'691'_402 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_402 = erased
-- Data.Integer.Properties._.IsAlternativeMagma.∙-congˡ
d_'8729''45'cong'737'_404 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_404 = erased
-- Data.Integer.Properties._.IsBand.assoc
d_assoc_408 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_408 = erased
-- Data.Integer.Properties._.IsBand.idem
d_idem_410 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_410 = erased
-- Data.Integer.Properties._.IsBand.isEquivalence
d_isEquivalence_412 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_412 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)))
-- Data.Integer.Properties._.IsBand.isMagma
d_isMagma_414 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0))
-- Data.Integer.Properties._.IsBand.isPartialEquivalence
d_isPartialEquivalence_416 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_416 ~v0 v1 = du_isPartialEquivalence_416 v1
du_isPartialEquivalence_416 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_416 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Integer.Properties._.IsBand.isSemigroup
d_isSemigroup_418 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_418 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)
-- Data.Integer.Properties._.IsBand.refl
d_refl_420 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_420 = erased
-- Data.Integer.Properties._.IsBand.reflexive
d_reflexive_422 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_422 = erased
-- Data.Integer.Properties._.IsBand.setoid
d_setoid_424 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_424 ~v0 v1 = du_setoid_424 v1
du_setoid_424 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_424 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Integer.Properties._.IsBand.sym
d_sym_426 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_426 = erased
-- Data.Integer.Properties._.IsBand.trans
d_trans_428 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_428 = erased
-- Data.Integer.Properties._.IsBand.∙-cong
d_'8729''45'cong_430 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_430 = erased
-- Data.Integer.Properties._.IsBand.∙-congʳ
d_'8729''45'cong'691'_432 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_432 = erased
-- Data.Integer.Properties._.IsBand.∙-congˡ
d_'8729''45'cong'737'_434 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_434 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-assoc
d_'42''45'assoc_438 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_438 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-cancelʳ-nonZero
d_'42''45'cancel'691''45'nonZero_440 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'691''45'nonZero_440 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_442 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45'nonZero_442 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-comm
d_'42''45'comm_444 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_444 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-cong
d_'42''45'cong_446 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_446 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_448 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_448 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_450 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_450 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-identity
d_'42''45'identity_452 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_452 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.identityʳ
d_identity'691'_454 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_454 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.identityˡ
d_identity'737'_456 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_456 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_458 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_458 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_458 v4
du_isCommutativeMagma_458 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_458 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
               (coe v2))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_460 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_460 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeMonoid_460 v4
du_'42''45'isCommutativeMonoid_460 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_460 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_462 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_462 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeSemigroup_462 v4
du_'42''45'isCommutativeSemigroup_462 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_462 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
            (coe v1)))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-isMagma
d_'42''45'isMagma_464 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_464 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_464 v4
du_'42''45'isMagma_464 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_464 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v2))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-isMonoid
d_'42''45'isMonoid_466 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_466 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_466 v4
du_'42''45'isMonoid_466 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_466 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v2))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.*-isSemigroup
d_'42''45'isSemigroup_468 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_468 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_468 v4
du_'42''45'isSemigroup_468 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_468 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v2))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.assoc
d_assoc_470 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_470 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.comm
d_comm_472 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_472 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.∙-cong
d_'8729''45'cong_474 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_474 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_476 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_476 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_478 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_478 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.identity
d_identity_480 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_480 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
                     (coe v0))))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.identityʳ
d_identity'691'_482 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_482 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.identityˡ
d_identity'737'_484 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_484 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_486 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_486 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_486 v4
du_isCommutativeMagma_486 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_486 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
                     (coe v4))))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_488 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_488 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_490 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_490 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_490 v4
du_isCommutativeSemigroup_490 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_490 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                  (coe v3)))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isMagma
d_isMagma_492 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_492 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
                        (coe v0)))))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isMonoid
d_isMonoid_494 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_494 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
                  (coe v0)))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isSemigroup
d_isSemigroup_496 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_496 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
                     (coe v0))))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isUnitalMagma
d_isUnitalMagma_498 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_498 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_498 v4
du_isUnitalMagma_498 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_498 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v4))))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.distrib
d_distrib_500 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_500 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.distribʳ
d_distrib'691'_502 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_502 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.distribˡ
d_distrib'737'_504 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_504 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_506 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_506 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
      (coe v0)
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_508 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_508 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemiringWithoutOne_508 v4
du_isCommutativeSemiringWithoutOne_508 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_508 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isEquivalence
d_isEquivalence_510 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_510 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
                           (coe v0))))))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isNearSemiring
d_isNearSemiring_512 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_512 ~v0 ~v1 ~v2 ~v3 v4 = du_isNearSemiring_512 v4
du_isNearSemiring_512 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_512 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
            (coe
               MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
               (coe v2))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isPartialEquivalence
d_isPartialEquivalence_514 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_514 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_514 v4
du_isPartialEquivalence_514 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_514 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                              (coe v7)))))))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isSemiring
d_isSemiring_516 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_516 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_518 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_518 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
            (coe v0)))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_520 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_520 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_520 v4
du_isSemiringWithoutOne_520 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_520 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1)))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.refl
d_refl_522 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_522 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.reflexive
d_reflexive_524 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_524 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.setoid
d_setoid_526 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_526 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_526 v4
du_setoid_526 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_526 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v6))))))))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.sym
d_sym_528 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_528 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.trans
d_trans_530 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_530 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.zero
d_zero_532 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_532 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
            (coe v0)))
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.zeroʳ
d_zero'691'_534 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_534 = erased
-- Data.Integer.Properties._.IsCancellativeCommutativeSemiring.zeroˡ
d_zero'737'_536 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_536 = erased
-- Data.Integer.Properties._.IsCommutativeBand.assoc
d_assoc_540 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_540 = erased
-- Data.Integer.Properties._.IsCommutativeBand.comm
d_comm_542 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_542 = erased
-- Data.Integer.Properties._.IsCommutativeBand.idem
d_idem_544 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_544 = erased
-- Data.Integer.Properties._.IsCommutativeBand.isBand
d_isBand_546 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_546 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Data.Integer.Properties._.IsCommutativeBand.isCommutativeMagma
d_isCommutativeMagma_548 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_548 ~v0 v1 = du_isCommutativeMagma_548 v1
du_isCommutativeMagma_548 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_548 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_654
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeBand.isCommutativeSemigroup
d_isCommutativeSemigroup_550 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_550 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_654 v1
-- Data.Integer.Properties._.IsCommutativeBand.isEquivalence
d_isEquivalence_552 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_552 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Data.Integer.Properties._.IsCommutativeBand.isMagma
d_isMagma_554 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_554 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Data.Integer.Properties._.IsCommutativeBand.isPartialEquivalence
d_isPartialEquivalence_556 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_556 ~v0 v1 = du_isPartialEquivalence_556 v1
du_isPartialEquivalence_556 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_556 v0
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
-- Data.Integer.Properties._.IsCommutativeBand.isSemigroup
d_isSemigroup_558 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_558 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Data.Integer.Properties._.IsCommutativeBand.refl
d_refl_560 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_560 = erased
-- Data.Integer.Properties._.IsCommutativeBand.reflexive
d_reflexive_562 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_562 = erased
-- Data.Integer.Properties._.IsCommutativeBand.setoid
d_setoid_564 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_564 ~v0 v1 = du_setoid_564 v1
du_setoid_564 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_564 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Integer.Properties._.IsCommutativeBand.sym
d_sym_566 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_566 = erased
-- Data.Integer.Properties._.IsCommutativeBand.trans
d_trans_568 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_568 = erased
-- Data.Integer.Properties._.IsCommutativeBand.∙-cong
d_'8729''45'cong_570 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_570 = erased
-- Data.Integer.Properties._.IsCommutativeBand.∙-congʳ
d_'8729''45'cong'691'_572 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_572 = erased
-- Data.Integer.Properties._.IsCommutativeBand.∙-congˡ
d_'8729''45'cong'737'_574 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_574 = erased
-- Data.Integer.Properties._.IsCommutativeMagma.comm
d_comm_578 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_578 = erased
-- Data.Integer.Properties._.IsCommutativeMagma.isEquivalence
d_isEquivalence_580 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_580 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0))
-- Data.Integer.Properties._.IsCommutativeMagma.isMagma
d_isMagma_582 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_582 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0)
-- Data.Integer.Properties._.IsCommutativeMagma.isPartialEquivalence
d_isPartialEquivalence_584 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_584 ~v0 v1 = du_isPartialEquivalence_584 v1
du_isPartialEquivalence_584 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_584 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsCommutativeMagma.refl
d_refl_586 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_586 = erased
-- Data.Integer.Properties._.IsCommutativeMagma.reflexive
d_reflexive_588 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_588 = erased
-- Data.Integer.Properties._.IsCommutativeMagma.setoid
d_setoid_590 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_590 ~v0 v1 = du_setoid_590 v1
du_setoid_590 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_590 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0))
-- Data.Integer.Properties._.IsCommutativeMagma.sym
d_sym_592 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_592 = erased
-- Data.Integer.Properties._.IsCommutativeMagma.trans
d_trans_594 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_594 = erased
-- Data.Integer.Properties._.IsCommutativeMagma.∙-cong
d_'8729''45'cong_596 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_596 = erased
-- Data.Integer.Properties._.IsCommutativeMagma.∙-congʳ
d_'8729''45'cong'691'_598 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_598 = erased
-- Data.Integer.Properties._.IsCommutativeMagma.∙-congˡ
d_'8729''45'cong'737'_600 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_600 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.assoc
d_assoc_604 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_604 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.comm
d_comm_606 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_606 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.identity
d_identity_608 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_608 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Integer.Properties._.IsCommutativeMonoid.identityʳ
d_identity'691'_610 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_610 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.identityˡ
d_identity'737'_612 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_612 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_614 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_614 ~v0 ~v1 v2 = du_isCommutativeMagma_614 v2
du_isCommutativeMagma_614 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_614 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_616 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_616 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814 v2
-- Data.Integer.Properties._.IsCommutativeMonoid.isEquivalence
d_isEquivalence_618 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_618 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))))
-- Data.Integer.Properties._.IsCommutativeMonoid.isMagma
d_isMagma_620 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_620 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)))
-- Data.Integer.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_622 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_622 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)
-- Data.Integer.Properties._.IsCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_624 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_624 ~v0 ~v1 v2
  = du_isPartialEquivalence_624 v2
du_isPartialEquivalence_624 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_624 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0) in
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
-- Data.Integer.Properties._.IsCommutativeMonoid.isSemigroup
d_isSemigroup_626 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_626 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Integer.Properties._.IsCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_628 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_628 ~v0 ~v1 v2 = du_isUnitalMagma_628 v2
du_isUnitalMagma_628 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_628 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Integer.Properties._.IsCommutativeMonoid.refl
d_refl_630 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_630 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.reflexive
d_reflexive_632 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_632 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.setoid
d_setoid_634 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_634 ~v0 ~v1 v2 = du_setoid_634 v2
du_setoid_634 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_634 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Integer.Properties._.IsCommutativeMonoid.sym
d_sym_636 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_636 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.trans
d_trans_638 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_638 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.∙-cong
d_'8729''45'cong_640 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_640 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_642 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_642 = erased
-- Data.Integer.Properties._.IsCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_644 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_644 = erased
-- Data.Integer.Properties._.IsCommutativeRing._//_
d__'47''47'__648 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> Integer -> Integer
d__'47''47'__648 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__648 v0 v2
du__'47''47'__648 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__648 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Integer.Properties._.IsCommutativeRing.*-assoc
d_'42''45'assoc_650 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_650 = erased
-- Data.Integer.Properties._.IsCommutativeRing.*-comm
d_'42''45'comm_652 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_652 = erased
-- Data.Integer.Properties._.IsCommutativeRing.*-cong
d_'42''45'cong_654 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_654 = erased
-- Data.Integer.Properties._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_656 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_656 = erased
-- Data.Integer.Properties._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_658 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_658 = erased
-- Data.Integer.Properties._.IsCommutativeRing.*-identity
d_'42''45'identity_660 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_660 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Integer.Properties._.IsCommutativeRing.identityʳ
d_identity'691'_662 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_662 = erased
-- Data.Integer.Properties._.IsCommutativeRing.identityˡ
d_identity'737'_664 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_664 = erased
-- Data.Integer.Properties._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_666 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_666 v0 v1 v2 v3 ~v4 v5
  = du_isCommutativeMagma_666 v0 v1 v2 v3 v5
du_isCommutativeMagma_666 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_666 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
               (coe v6))))
-- Data.Integer.Properties._.IsCommutativeRing.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_668 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_668 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isCommutativeMonoid_668 v0 v1 v2 v3 v5
du_'42''45'isCommutativeMonoid_668 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_668 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Integer.Properties._.IsCommutativeRing.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_670 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_670 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isCommutativeSemigroup_670 v0 v1 v2 v3 v5
du_'42''45'isCommutativeSemigroup_670 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_670 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
            (coe v5)))
-- Data.Integer.Properties._.IsCommutativeRing.*-isMagma
d_'42''45'isMagma_672 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_672 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMagma_672 v0 v1 v2 v3 v5
du_'42''45'isMagma_672 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_672 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Data.Integer.Properties._.IsCommutativeRing.*-isMonoid
d_'42''45'isMonoid_674 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_674 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMonoid_674 v0 v1 v2 v3 v5
du_'42''45'isMonoid_674 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_674 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2860 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4))
-- Data.Integer.Properties._.IsCommutativeRing.*-isSemigroup
d_'42''45'isSemigroup_676 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_676 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isSemigroup_676 v0 v1 v2 v3 v5
du_'42''45'isSemigroup_676 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_676 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Data.Integer.Properties._.IsCommutativeRing.assoc
d_assoc_678 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_678 = erased
-- Data.Integer.Properties._.IsCommutativeRing.comm
d_comm_680 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_680 = erased
-- Data.Integer.Properties._.IsCommutativeRing.∙-cong
d_'8729''45'cong_682 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_682 = erased
-- Data.Integer.Properties._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_684 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_684 = erased
-- Data.Integer.Properties._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_686 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_686 = erased
-- Data.Integer.Properties._.IsCommutativeRing.identity
d_identity_688 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_688 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_688 v5
du_identity_688 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_688 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_724
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
                  (coe v1)))))
-- Data.Integer.Properties._.IsCommutativeRing.identityʳ
d_identity'691'_690 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_690 = erased
-- Data.Integer.Properties._.IsCommutativeRing.identityˡ
d_identity'737'_692 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_692 = erased
-- Data.Integer.Properties._.IsCommutativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_694 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_694 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Integer.Properties._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_696 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_696 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_696 v5
du_isCommutativeMagma_696 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_696 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
                     (coe v4))))))
-- Data.Integer.Properties._.IsCommutativeRing.isCommutativeMonoid
d_isCommutativeMonoid_698 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_698 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_698 v5
du_isCommutativeMonoid_698 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_698 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
               (coe v2))))
-- Data.Integer.Properties._.IsCommutativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_700 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_700 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_700 v5
du_isCommutativeSemigroup_700 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_700 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
                  (coe v3)))))
-- Data.Integer.Properties._.IsCommutativeRing.isGroup
d_isGroup_702 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_702 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_702 v5
du_isGroup_702 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
du_isGroup_702 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v1)))
-- Data.Integer.Properties._.IsCommutativeRing.isInvertibleMagma
d_isInvertibleMagma_704 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_704 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_704 v5
du_isInvertibleMagma_704 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_704 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v3)))))
-- Data.Integer.Properties._.IsCommutativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_706 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_706 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_706 v5
du_isInvertibleUnitalMagma_706 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_706 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v3)))))
-- Data.Integer.Properties._.IsCommutativeRing.isMagma
d_isMagma_708 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_708 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_708 v5
du_isMagma_708 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_708 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
                     (coe v1))))))
-- Data.Integer.Properties._.IsCommutativeRing.isMonoid
d_isMonoid_710 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_710 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_710 v5
du_isMonoid_710 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_isMonoid_710 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
               (coe v1))))
-- Data.Integer.Properties._.IsCommutativeRing.isSemigroup
d_isSemigroup_712 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_712 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_712 v5
du_isSemigroup_712 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_712 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
                  (coe v1)))))
-- Data.Integer.Properties._.IsCommutativeRing.isUnitalMagma
d_isUnitalMagma_714 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_714 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_714 v5
du_isUnitalMagma_714 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_714 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v4))))))
-- Data.Integer.Properties._.IsCommutativeRing.⁻¹-cong
d_'8315''185''45'cong_716 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_716 = erased
-- Data.Integer.Properties._.IsCommutativeRing.inverse
d_inverse_718 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_718 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_718 v5
du_inverse_718 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_718 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_inverse_1090
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
               (coe v1))))
-- Data.Integer.Properties._.IsCommutativeRing.inverseʳ
d_inverse'691'_720 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_720 = erased
-- Data.Integer.Properties._.IsCommutativeRing.inverseˡ
d_inverse'737'_722 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_722 = erased
-- Data.Integer.Properties._.IsCommutativeRing.distrib
d_distrib_724 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_724 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2770
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Integer.Properties._.IsCommutativeRing.distribʳ
d_distrib'691'_726 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_726 = erased
-- Data.Integer.Properties._.IsCommutativeRing.distribˡ
d_distrib'737'_728 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_728 = erased
-- Data.Integer.Properties._.IsCommutativeRing.isCommutativeSemiring
d_isCommutativeSemiring_730 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_730 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018 v0 v1
      v2 v3 v5
-- Data.Integer.Properties._.IsCommutativeRing.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_732 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_732 v0 v1 v2 v3 ~v4 v5
  = du_isCommutativeSemiringWithoutOne_732 v0 v1 v2 v3 v5
du_isCommutativeSemiringWithoutOne_732 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_732 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Integer.Properties._.IsCommutativeRing.isEquivalence
d_isEquivalence_734 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_734 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_734 v5
du_isEquivalence_734 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_734 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
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
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
                        (coe v1)))))))
-- Data.Integer.Properties._.IsCommutativeRing.isNearSemiring
d_isNearSemiring_736 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_736 v0 v1 v2 v3 ~v4 v5
  = du_isNearSemiring_736 v0 v1 v2 v3 v5
du_isNearSemiring_736 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_736 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v5)))
-- Data.Integer.Properties._.IsCommutativeRing.isPartialEquivalence
d_isPartialEquivalence_738 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_738 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_738 v5
du_isPartialEquivalence_738 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_738 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                              (coe v7)))))))))
-- Data.Integer.Properties._.IsCommutativeRing.isRing
d_isRing_740 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_isRing_740 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0)
-- Data.Integer.Properties._.IsCommutativeRing.isRingWithoutOne
d_isRingWithoutOne_742 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
d_isRingWithoutOne_742 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isRingWithoutOne_742 v5
du_isRingWithoutOne_742 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
du_isRingWithoutOne_742 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Integer.Properties._.IsCommutativeRing.isSemiring
d_isSemiring_744 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_744 v0 v1 v2 v3 ~v4 v5
  = du_isSemiring_744 v0 v1 v2 v3 v5
du_isSemiring_744 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
du_isSemiring_744 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4))
-- Data.Integer.Properties._.IsCommutativeRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_746 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_746 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isSemiringWithoutAnnihilatingZero_746 v5
du_isSemiringWithoutAnnihilatingZero_746 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
du_isSemiringWithoutAnnihilatingZero_746 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2868
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Integer.Properties._.IsCommutativeRing.isSemiringWithoutOne
d_isSemiringWithoutOne_748 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_748 v0 v1 v2 v3 ~v4 v5
  = du_isSemiringWithoutOne_748 v0 v1 v2 v3 v5
du_isSemiringWithoutOne_748 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_748 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Data.Integer.Properties._.IsCommutativeRing.refl
d_refl_750 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_750 = erased
-- Data.Integer.Properties._.IsCommutativeRing.reflexive
d_reflexive_752 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_752 = erased
-- Data.Integer.Properties._.IsCommutativeRing.setoid
d_setoid_754 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_754 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_754 v5
du_setoid_754 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_754 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v6))))))))
-- Data.Integer.Properties._.IsCommutativeRing.sym
d_sym_756 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_756 = erased
-- Data.Integer.Properties._.IsCommutativeRing.trans
d_trans_758 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_758 = erased
-- Data.Integer.Properties._.IsCommutativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_760 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_760 = erased
-- Data.Integer.Properties._.IsCommutativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_762 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_762 = erased
-- Data.Integer.Properties._.IsCommutativeRing.zero
d_zero_764 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_764 v0 v1 v2 v3 ~v4 v5 = du_zero_764 v0 v1 v2 v3 v5
du_zero_764 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_764 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero_2468 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v5)))
-- Data.Integer.Properties._.IsCommutativeRing.zeroʳ
d_zero'691'_766 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_766 = erased
-- Data.Integer.Properties._.IsCommutativeRing.zeroˡ
d_zero'737'_768 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_768 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.assoc
d_assoc_772 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_772 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.comm
d_comm_774 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_774 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.isCommutativeMagma
d_isCommutativeMagma_776 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_776 v0 v1
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606 v1
-- Data.Integer.Properties._.IsCommutativeSemigroup.isEquivalence
d_isEquivalence_778 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_778 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)))
-- Data.Integer.Properties._.IsCommutativeSemigroup.isMagma
d_isMagma_780 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_780 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemigroup.isPartialEquivalence
d_isPartialEquivalence_782 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_782 ~v0 v1 = du_isPartialEquivalence_782 v1
du_isPartialEquivalence_782 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_782 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Integer.Properties._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_784 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)
-- Data.Integer.Properties._.IsCommutativeSemigroup.refl
d_refl_786 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_786 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.reflexive
d_reflexive_788 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_788 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.setoid
d_setoid_790 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_790 ~v0 v1 = du_setoid_790 v1
du_setoid_790 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_790 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Integer.Properties._.IsCommutativeSemigroup.sym
d_sym_792 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_792 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.trans
d_trans_794 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_794 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.∙-cong
d_'8729''45'cong_796 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_796 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.∙-congʳ
d_'8729''45'cong'691'_798 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_798 = erased
-- Data.Integer.Properties._.IsCommutativeSemigroup.∙-congˡ
d_'8729''45'cong'737'_800 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_800 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.*-assoc
d_'42''45'assoc_804 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_804 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.*-comm
d_'42''45'comm_806 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_806 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.*-cong
d_'42''45'cong_808 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_808 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_810 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_810 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_812 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_812 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.*-identity
d_'42''45'identity_814 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_814 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Integer.Properties._.IsCommutativeSemiring.identityʳ
d_identity'691'_816 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_816 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.identityˡ
d_identity'737'_818 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_818 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_820 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_820 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_820 v4
du_isCommutativeMagma_820 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_820 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
            (coe v1)))
-- Data.Integer.Properties._.IsCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_822 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_822 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      v4
-- Data.Integer.Properties._.IsCommutativeSemiring.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_824 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_824 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeSemigroup_824 v4
du_'42''45'isCommutativeSemigroup_824 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_824 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiring.*-isMagma
d_'42''45'isMagma_826 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_826 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_826 v4
du_'42''45'isMagma_826 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_826 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Integer.Properties._.IsCommutativeSemiring.*-isMonoid
d_'42''45'isMonoid_828 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_828 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_828 v4
du_'42''45'isMonoid_828 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_828 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Integer.Properties._.IsCommutativeSemiring.*-isSemigroup
d_'42''45'isSemigroup_830 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_830 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_830 v4
du_'42''45'isSemigroup_830 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_830 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Integer.Properties._.IsCommutativeSemiring.assoc
d_assoc_832 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_832 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.comm
d_comm_834 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_834 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.∙-cong
d_'8729''45'cong_836 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_836 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_838 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_838 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_840 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_840 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.identity
d_identity_842 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_842 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))))
-- Data.Integer.Properties._.IsCommutativeSemiring.identityʳ
d_identity'691'_844 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_844 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.identityˡ
d_identity'737'_846 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_846 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_848 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_848 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_848 v4
du_isCommutativeMagma_848 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_848 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
                  (coe v3)))))
-- Data.Integer.Properties._.IsCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_850 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_850 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Integer.Properties._.IsCommutativeSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_852 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_852 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_852 v4
du_isCommutativeSemigroup_852 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_852 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe v2))))
-- Data.Integer.Properties._.IsCommutativeSemiring.isMagma
d_isMagma_854 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_854 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))))))
-- Data.Integer.Properties._.IsCommutativeSemiring.isMonoid
d_isMonoid_856 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_856 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))))
-- Data.Integer.Properties._.IsCommutativeSemiring.isSemigroup
d_isSemigroup_858 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_858 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))))
-- Data.Integer.Properties._.IsCommutativeSemiring.isUnitalMagma
d_isUnitalMagma_860 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_860 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_860 v4
du_isUnitalMagma_860 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_860 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
               (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v3)))))
-- Data.Integer.Properties._.IsCommutativeSemiring.distrib
d_distrib_862 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_862 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Integer.Properties._.IsCommutativeSemiring.distribʳ
d_distrib'691'_864 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_864 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.distribˡ
d_distrib'737'_866 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_866 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_868 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_868 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      v4
-- Data.Integer.Properties._.IsCommutativeSemiring.isEquivalence
d_isEquivalence_870 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_870 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))))))
-- Data.Integer.Properties._.IsCommutativeSemiring.isNearSemiring
d_isNearSemiring_872 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_872 ~v0 ~v1 ~v2 ~v3 v4 = du_isNearSemiring_872 v4
du_isNearSemiring_872 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_872 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
            (coe v1)))
-- Data.Integer.Properties._.IsCommutativeSemiring.isPartialEquivalence
d_isPartialEquivalence_874 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_874 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_874 v4
du_isPartialEquivalence_874 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_874 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v6))))))))
-- Data.Integer.Properties._.IsCommutativeSemiring.isSemiring
d_isSemiring_876 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_876 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)
-- Data.Integer.Properties._.IsCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_878 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_878 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_880 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_880 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_880 v4
du_isSemiringWithoutOne_880 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_880 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiring.refl
d_refl_882 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_882 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.reflexive
d_reflexive_884 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_884 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.setoid
d_setoid_886 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_886 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_886 v4
du_setoid_886 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_886 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_202
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v5)))))))
-- Data.Integer.Properties._.IsCommutativeSemiring.sym
d_sym_888 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_888 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.trans
d_trans_890 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_890 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.zero
d_zero_892 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_892 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiring.zeroʳ
d_zero'691'_894 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_894 = erased
-- Data.Integer.Properties._.IsCommutativeSemiring.zeroˡ
d_zero'737'_896 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_896 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.*-assoc
d_'42''45'assoc_900 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_900 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_902 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_902 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.*-cong
d_'42''45'cong_904 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_904 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_906 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_906 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_908 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_908 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_910 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_910 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_910 v3
du_isCommutativeMagma_910 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_910 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_912 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_912 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
      v3
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_914 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_914 ~v0 ~v1 ~v2 v3 = du_'42''45'isMagma_914 v3
du_'42''45'isMagma_914 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_914 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1410
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_916 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_916 ~v0 ~v1 ~v2 v3
  = du_'42''45'isSemigroup_916 v3
du_'42''45'isSemigroup_916 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_916 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1412
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.assoc
d_assoc_918 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_918 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.comm
d_comm_920 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_920 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.∙-cong
d_'8729''45'cong_922 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_922 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_924 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_924 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_926 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_926 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.identity
d_identity_928 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_928 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
               (coe v0))))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.identityʳ
d_identity'691'_930 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_930 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.identityˡ
d_identity'737'_932 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_932 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_934 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_934 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_934 v3
du_isCommutativeMagma_934 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_934 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
               (coe v2))))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_936 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_936 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_938 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_938 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_938 v3
du_isCommutativeSemigroup_938 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_938 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe v1)))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.isMonoid
d_isMonoid_940 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_940 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
            (coe v0)))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.distrib
d_distrib_942 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_942 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1366
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.distribʳ
d_distrib'691'_944 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_944 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.distribˡ
d_distrib'737'_946 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_946 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.isEquivalence
d_isEquivalence_948 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_948 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
                     (coe v0))))))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.isNearSemiring
d_isNearSemiring_950 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_950 ~v0 ~v1 ~v2 v3 = du_isNearSemiring_950 v3
du_isNearSemiring_950 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_950 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.isPartialEquivalence
d_isPartialEquivalence_952 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_952 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_952 v3
du_isPartialEquivalence_952 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_952 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
                        (coe v1)))))))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_954 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_954 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
      (coe v0)
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.refl
d_refl_956 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_956 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.reflexive
d_reflexive_958 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_958 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.setoid
d_setoid_960 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_960 ~v0 ~v1 ~v2 v3 = du_setoid_960 v3
du_setoid_960 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_960 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4))))))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.sym
d_sym_962 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_962 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.trans
d_trans_964 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_964 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.zero
d_zero_966 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_966 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1368
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.zeroʳ
d_zero'691'_968 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_968 = erased
-- Data.Integer.Properties._.IsCommutativeSemiringWithoutOne.zeroˡ
d_zero'737'_970 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_970 = erased
-- Data.Integer.Properties._.IsFlexibleMagma.flex
d_flex_974 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flex_974 = erased
-- Data.Integer.Properties._.IsFlexibleMagma.isEquivalence
d_isEquivalence_976 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_976 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0))
-- Data.Integer.Properties._.IsFlexibleMagma.isMagma
d_isMagma_978 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_978 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0)
-- Data.Integer.Properties._.IsFlexibleMagma.isPartialEquivalence
d_isPartialEquivalence_980 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_980 ~v0 v1 = du_isPartialEquivalence_980 v1
du_isPartialEquivalence_980 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_980 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsFlexibleMagma.refl
d_refl_982 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_982 = erased
-- Data.Integer.Properties._.IsFlexibleMagma.reflexive
d_reflexive_984 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_984 = erased
-- Data.Integer.Properties._.IsFlexibleMagma.setoid
d_setoid_986 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_986 ~v0 v1 = du_setoid_986 v1
du_setoid_986 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_986 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0))
-- Data.Integer.Properties._.IsFlexibleMagma.sym
d_sym_988 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_988 = erased
-- Data.Integer.Properties._.IsFlexibleMagma.trans
d_trans_990 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_990 = erased
-- Data.Integer.Properties._.IsFlexibleMagma.∙-cong
d_'8729''45'cong_992 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_992 = erased
-- Data.Integer.Properties._.IsFlexibleMagma.∙-congʳ
d_'8729''45'cong'691'_994 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_994 = erased
-- Data.Integer.Properties._.IsFlexibleMagma.∙-congˡ
d_'8729''45'cong'737'_996 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_996 = erased
-- Data.Integer.Properties._.IsGroup._-_
d__'45'__1000 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> Integer -> Integer
d__'45'__1000 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du__'45'__1142 v0 v2
-- Data.Integer.Properties._.IsGroup._//_
d__'47''47'__1002 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> Integer -> Integer
d__'47''47'__1002 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 v0 v2 v4 v5
-- Data.Integer.Properties._.IsGroup._\\_
d__'92''92'__1004 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> Integer -> Integer
d__'92''92'__1004 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du__'92''92'__1130 v0 v2 v4 v5
-- Data.Integer.Properties._.IsGroup.assoc
d_assoc_1006 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1006 = erased
-- Data.Integer.Properties._.IsGroup.identity
d_identity_1008 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1008 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Integer.Properties._.IsGroup.identityʳ
d_identity'691'_1010 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1010 = erased
-- Data.Integer.Properties._.IsGroup.identityˡ
d_identity'737'_1012 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1012 = erased
-- Data.Integer.Properties._.IsGroup.inverse
d_inverse_1014 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1014 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1090 (coe v0)
-- Data.Integer.Properties._.IsGroup.inverseʳ
d_inverse'691'_1016 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1016 = erased
-- Data.Integer.Properties._.IsGroup.inverseˡ
d_inverse'737'_1018 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1018 = erased
-- Data.Integer.Properties._.IsGroup.isEquivalence
d_isEquivalence_1020 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1020 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))))
-- Data.Integer.Properties._.IsGroup.isInvertibleMagma
d_isInvertibleMagma_1022 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1022 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160 v3
-- Data.Integer.Properties._.IsGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1024 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_1024 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162 v3
-- Data.Integer.Properties._.IsGroup.isMagma
d_isMagma_1026 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1026 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)))
-- Data.Integer.Properties._.IsGroup.isMonoid
d_isMonoid_1028 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1028 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)
-- Data.Integer.Properties._.IsGroup.isPartialEquivalence
d_isPartialEquivalence_1030 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1030 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1030 v3
du_isPartialEquivalence_1030 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1030 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0) in
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
-- Data.Integer.Properties._.IsGroup.isSemigroup
d_isSemigroup_1032 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1032 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Integer.Properties._.IsGroup.isUnitalMagma
d_isUnitalMagma_1034 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1034 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_1034 v3
du_isUnitalMagma_1034 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1034 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Integer.Properties._.IsGroup.refl
d_refl_1036 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1036 = erased
-- Data.Integer.Properties._.IsGroup.reflexive
d_reflexive_1038 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1038 = erased
-- Data.Integer.Properties._.IsGroup.setoid
d_setoid_1040 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1040 ~v0 ~v1 ~v2 v3 = du_setoid_1040 v3
du_setoid_1040 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1040 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Integer.Properties._.IsGroup.sym
d_sym_1042 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1042 = erased
-- Data.Integer.Properties._.IsGroup.trans
d_trans_1044 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1044 = erased
-- Data.Integer.Properties._.IsGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_1046 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_1046 = erased
-- Data.Integer.Properties._.IsGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_1048 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_1048 = erased
-- Data.Integer.Properties._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_1050 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1050 = erased
-- Data.Integer.Properties._.IsGroup.∙-cong
d_'8729''45'cong_1052 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1052 = erased
-- Data.Integer.Properties._.IsGroup.∙-congʳ
d_'8729''45'cong'691'_1054 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1054 = erased
-- Data.Integer.Properties._.IsGroup.∙-congˡ
d_'8729''45'cong'737'_1056 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1056 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.assoc
d_assoc_1060 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1060 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.comm
d_comm_1062 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1062 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.idem
d_idem_1064 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1064 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.identity
d_identity_1066 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1066 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.identityʳ
d_identity'691'_1068 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1068 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.identityˡ
d_identity'737'_1070 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1070 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isBand
d_isBand_1072 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1072 ~v0 ~v1 v2 = du_isBand_1072 v2
du_isBand_1072 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1072 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isCommutativeBand
d_isCommutativeBand_1074 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1074 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 v2
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_1076 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1076 ~v0 ~v1 v2
  = du_isCommutativeMagma_1076 v2
du_isCommutativeMagma_1076 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1076 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_1078 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_1078 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0)
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_1080 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1080 ~v0 ~v1 v2
  = du_isCommutativeSemigroup_1080 v2
du_isCommutativeSemigroup_1080 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1080 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isEquivalence
d_isEquivalence_1082 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1082 v0
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
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isIdempotentMonoid
d_isIdempotentMonoid_1084 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1084 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 v2
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isMagma
d_isMagma_1086 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1086 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
               (coe v0))))
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isMonoid
d_isMonoid_1088 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1088 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_1090 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1090 ~v0 ~v1 v2
  = du_isPartialEquivalence_1090 v2
du_isPartialEquivalence_1090 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1090 v0
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
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isSemigroup
d_isSemigroup_1092 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1092 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_1094 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1094 ~v0 ~v1 v2 = du_isUnitalMagma_1094 v2
du_isUnitalMagma_1094 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1094 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.refl
d_refl_1096 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1096 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.reflexive
d_reflexive_1098 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1098 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.setoid
d_setoid_1100 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1100 ~v0 ~v1 v2 = du_setoid_1100 v2
du_setoid_1100 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1100 v0
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
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.sym
d_sym_1102 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1102 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.trans
d_trans_1104 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1104 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.∙-cong
d_'8729''45'cong_1106 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1106 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_1108 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1108 = erased
-- Data.Integer.Properties._.IsIdempotentCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_1110 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1110 = erased
-- Data.Integer.Properties._.IsIdempotentMagma.idem
d_idem_1114 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1114 = erased
-- Data.Integer.Properties._.IsIdempotentMagma.isEquivalence
d_isEquivalence_1116 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1116 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0))
-- Data.Integer.Properties._.IsIdempotentMagma.isMagma
d_isMagma_1118 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1118 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0)
-- Data.Integer.Properties._.IsIdempotentMagma.isPartialEquivalence
d_isPartialEquivalence_1120 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1120 ~v0 v1
  = du_isPartialEquivalence_1120 v1
du_isPartialEquivalence_1120 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1120 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsIdempotentMagma.refl
d_refl_1122 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1122 = erased
-- Data.Integer.Properties._.IsIdempotentMagma.reflexive
d_reflexive_1124 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1124 = erased
-- Data.Integer.Properties._.IsIdempotentMagma.setoid
d_setoid_1126 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1126 ~v0 v1 = du_setoid_1126 v1
du_setoid_1126 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1126 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0))
-- Data.Integer.Properties._.IsIdempotentMagma.sym
d_sym_1128 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1128 = erased
-- Data.Integer.Properties._.IsIdempotentMagma.trans
d_trans_1130 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1130 = erased
-- Data.Integer.Properties._.IsIdempotentMagma.∙-cong
d_'8729''45'cong_1132 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1132 = erased
-- Data.Integer.Properties._.IsIdempotentMagma.∙-congʳ
d_'8729''45'cong'691'_1134 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1134 = erased
-- Data.Integer.Properties._.IsIdempotentMagma.∙-congˡ
d_'8729''45'cong'737'_1136 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1136 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.assoc
d_assoc_1140 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1140 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.idem
d_idem_1142 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1142 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.identity
d_identity_1144 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1144 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Integer.Properties._.IsIdempotentMonoid.identityʳ
d_identity'691'_1146 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1146 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.identityˡ
d_identity'737'_1148 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1148 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.isBand
d_isBand_1150 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1150 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isBand_876 v2
-- Data.Integer.Properties._.IsIdempotentMonoid.isEquivalence
d_isEquivalence_1152 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1152 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))))
-- Data.Integer.Properties._.IsIdempotentMonoid.isMagma
d_isMagma_1154 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0)))
-- Data.Integer.Properties._.IsIdempotentMonoid.isMonoid
d_isMonoid_1156 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1156 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0)
-- Data.Integer.Properties._.IsIdempotentMonoid.isPartialEquivalence
d_isPartialEquivalence_1158 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1158 ~v0 ~v1 v2
  = du_isPartialEquivalence_1158 v2
du_isPartialEquivalence_1158 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1158 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0) in
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
-- Data.Integer.Properties._.IsIdempotentMonoid.isSemigroup
d_isSemigroup_1160 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1160 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Integer.Properties._.IsIdempotentMonoid.isUnitalMagma
d_isUnitalMagma_1162 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1162 ~v0 ~v1 v2 = du_isUnitalMagma_1162 v2
du_isUnitalMagma_1162 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1162 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Integer.Properties._.IsIdempotentMonoid.refl
d_refl_1164 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1164 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.reflexive
d_reflexive_1166 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1166 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.setoid
d_setoid_1168 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1168 ~v0 ~v1 v2 = du_setoid_1168 v2
du_setoid_1168 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1168 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Integer.Properties._.IsIdempotentMonoid.sym
d_sym_1170 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1170 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.trans
d_trans_1172 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1172 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.∙-cong
d_'8729''45'cong_1174 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1174 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.∙-congʳ
d_'8729''45'cong'691'_1176 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1176 = erased
-- Data.Integer.Properties._.IsIdempotentMonoid.∙-congˡ
d_'8729''45'cong'737'_1178 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1178 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.*-assoc
d_'42''45'assoc_1182 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1182 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.*-cong
d_'42''45'cong_1184 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1184 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.∙-congʳ
d_'8729''45'cong'691'_1186 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1186 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.∙-congˡ
d_'8729''45'cong'737'_1188 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1188 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.*-identity
d_'42''45'identity_1190 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1190 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Integer.Properties._.IsIdempotentSemiring.identityʳ
d_identity'691'_1192 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1192 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.identityˡ
d_identity'737'_1194 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1194 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.*-isMagma
d_'42''45'isMagma_1196 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1196 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_1196 v4
du_'42''45'isMagma_1196 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1196 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Integer.Properties._.IsIdempotentSemiring.*-isMonoid
d_'42''45'isMonoid_1198 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1198 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_1198 v4
du_'42''45'isMonoid_1198 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1198 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Integer.Properties._.IsIdempotentSemiring.*-isSemigroup
d_'42''45'isSemigroup_1200 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1200 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_1200 v4
du_'42''45'isSemigroup_1200 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1200 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Integer.Properties._.IsIdempotentSemiring.assoc
d_assoc_1202 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1202 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.comm
d_comm_1204 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1204 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.∙-cong
d_'8729''45'cong_1206 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1206 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.∙-congʳ
d_'8729''45'cong'691'_1208 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1208 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.∙-congˡ
d_'8729''45'cong'737'_1210 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1210 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.+-idem
d_'43''45'idem_1212 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1212 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.identity
d_identity_1214 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1214 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))))
-- Data.Integer.Properties._.IsIdempotentSemiring.identityʳ
d_identity'691'_1216 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1216 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.identityˡ
d_identity'737'_1218 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1218 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.isBand
d_isBand_1220 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1220 ~v0 ~v1 ~v2 ~v3 v4 = du_isBand_1220 v4
du_isBand_1220 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1220 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isBand_876
         (coe
            MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
            (coe v1)))
-- Data.Integer.Properties._.IsIdempotentSemiring.isCommutativeBand
d_isCommutativeBand_1222 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1222 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeBand_1222 v4
du_isCommutativeBand_1222 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_1222 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
      (coe
         MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
         (coe v0))
-- Data.Integer.Properties._.IsIdempotentSemiring.isCommutativeMagma
d_isCommutativeMagma_1224 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1224 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_1224 v4
du_isCommutativeMagma_1224 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1224 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
                  (coe v3)))))
-- Data.Integer.Properties._.IsIdempotentSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1226 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1226 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Integer.Properties._.IsIdempotentSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_1228 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1228 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_1228 v4
du_isCommutativeSemigroup_1228 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1228 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe v2))))
-- Data.Integer.Properties._.IsIdempotentSemiring.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_1230 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_1230 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
      v4
-- Data.Integer.Properties._.IsIdempotentSemiring.isIdempotentMonoid
d_isIdempotentMonoid_1232 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1232 ~v0 ~v1 ~v2 ~v3 v4
  = du_isIdempotentMonoid_1232 v4
du_isIdempotentMonoid_1232 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_1232 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
      (coe
         MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
         (coe v0))
-- Data.Integer.Properties._.IsIdempotentSemiring.isMagma
d_isMagma_1234 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1234 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))))))
-- Data.Integer.Properties._.IsIdempotentSemiring.isMonoid
d_isMonoid_1236 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1236 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))))
-- Data.Integer.Properties._.IsIdempotentSemiring.isSemigroup
d_isSemigroup_1238 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1238 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))))
-- Data.Integer.Properties._.IsIdempotentSemiring.isUnitalMagma
d_isUnitalMagma_1240 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1240 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_1240 v4
du_isUnitalMagma_1240 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1240 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
               (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v3)))))
-- Data.Integer.Properties._.IsIdempotentSemiring.distrib
d_distrib_1242 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1242 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Integer.Properties._.IsIdempotentSemiring.distribʳ
d_distrib'691'_1244 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1244 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.distribˡ
d_distrib'737'_1246 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1246 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.isEquivalence
d_isEquivalence_1248 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1248 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))))))
-- Data.Integer.Properties._.IsIdempotentSemiring.isNearSemiring
d_isNearSemiring_1250 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_1250 ~v0 ~v1 ~v2 ~v3 v4
  = du_isNearSemiring_1250 v4
du_isNearSemiring_1250 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_1250 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
            (coe v1)))
-- Data.Integer.Properties._.IsIdempotentSemiring.isPartialEquivalence
d_isPartialEquivalence_1252 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1252 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1252 v4
du_isPartialEquivalence_1252 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1252 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v6))))))))
-- Data.Integer.Properties._.IsIdempotentSemiring.isSemiring
d_isSemiring_1254 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_1254 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)
-- Data.Integer.Properties._.IsIdempotentSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1256 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Integer.Properties._.IsIdempotentSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_1258 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1258 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_1258 v4
du_isSemiringWithoutOne_1258 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1258 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Integer.Properties._.IsIdempotentSemiring.refl
d_refl_1260 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1260 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.reflexive
d_reflexive_1262 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1262 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.setoid
d_setoid_1264 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1264 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1264 v4
du_setoid_1264 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1264 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_202
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v5)))))))
-- Data.Integer.Properties._.IsIdempotentSemiring.sym
d_sym_1266 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1266 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.trans
d_trans_1268 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1268 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.zero
d_zero_1270 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Integer.Properties._.IsIdempotentSemiring.zeroʳ
d_zero'691'_1272 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1272 = erased
-- Data.Integer.Properties._.IsIdempotentSemiring.zeroˡ
d_zero'737'_1274 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1274 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.inverse
d_inverse_1278 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1278 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_974 (coe v0)
-- Data.Integer.Properties._.IsInvertibleMagma.inverseʳ
d_inverse'691'_1280 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1280 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.inverseˡ
d_inverse'737'_1282 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1282 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.isEquivalence
d_isEquivalence_1284 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1284 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0))
-- Data.Integer.Properties._.IsInvertibleMagma.isMagma
d_isMagma_1286 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1286 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0)
-- Data.Integer.Properties._.IsInvertibleMagma.isPartialEquivalence
d_isPartialEquivalence_1288 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1288 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1288 v3
du_isPartialEquivalence_1288 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1288 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsInvertibleMagma.refl
d_refl_1290 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1290 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.reflexive
d_reflexive_1292 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1292 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.setoid
d_setoid_1294 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1294 ~v0 ~v1 ~v2 v3 = du_setoid_1294 v3
du_setoid_1294 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1294 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0))
-- Data.Integer.Properties._.IsInvertibleMagma.sym
d_sym_1296 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1296 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.trans
d_trans_1298 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1298 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_1300 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1300 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.∙-cong
d_'8729''45'cong_1302 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1302 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.∙-congʳ
d_'8729''45'cong'691'_1304 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1304 = erased
-- Data.Integer.Properties._.IsInvertibleMagma.∙-congˡ
d_'8729''45'cong'737'_1306 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1306 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.identity
d_identity_1310 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1310 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_1026 (coe v0)
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.identityʳ
d_identity'691'_1312 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1312 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.identityˡ
d_identity'737'_1314 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1314 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.inverse
d_inverse_1316 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1316 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_974
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0))
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.inverseʳ
d_inverse'691'_1318 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1318 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.inverseˡ
d_inverse'737'_1320 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1320 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.isEquivalence
d_isEquivalence_1322 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1322 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_972
         (coe
            MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0)))
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_1324 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0)
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.isMagma
d_isMagma_1326 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1326 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_972
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0))
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.isPartialEquivalence
d_isPartialEquivalence_1328 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1328 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1328 v3
du_isPartialEquivalence_1328 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1328 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024
              (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.isUnitalMagma
d_isUnitalMagma_1330 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1330 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_1064 v3
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.refl
d_refl_1332 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1332 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.reflexive
d_reflexive_1334 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1334 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.setoid
d_setoid_1336 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1336 ~v0 ~v1 ~v2 v3 = du_setoid_1336 v3
du_setoid_1336 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1336 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v1)))
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.sym
d_sym_1338 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1338 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.trans
d_trans_1340 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1340 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.⁻¹-cong
d_'8315''185''45'cong_1342 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1342 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.∙-cong
d_'8729''45'cong_1344 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1344 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.∙-congʳ
d_'8729''45'cong'691'_1346 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1346 = erased
-- Data.Integer.Properties._.IsInvertibleUnitalMagma.∙-congˡ
d_'8729''45'cong'737'_1348 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1348 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.*-assoc
d_'42''45'assoc_1352 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1352 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.*-cong
d_'42''45'cong_1354 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1354 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.∙-congʳ
d_'8729''45'cong'691'_1356 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1356 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.∙-congˡ
d_'8729''45'cong'737'_1358 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1358 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.*-identity
d_'42''45'identity_1360 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1360 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Integer.Properties._.IsKleeneAlgebra.identityʳ
d_identity'691'_1362 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1362 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.identityˡ
d_identity'737'_1364 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1364 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.*-isMagma
d_'42''45'isMagma_1366 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1366 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMagma_1366 v5
du_'42''45'isMagma_1366 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1366 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v2))))
-- Data.Integer.Properties._.IsKleeneAlgebra.*-isMonoid
d_'42''45'isMonoid_1368 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1368 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMonoid_1368 v5
du_'42''45'isMonoid_1368 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1368 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v2))))
-- Data.Integer.Properties._.IsKleeneAlgebra.*-isSemigroup
d_'42''45'isSemigroup_1370 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1370 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isSemigroup_1370 v5
du_'42''45'isSemigroup_1370 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1370 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v2))))
-- Data.Integer.Properties._.IsKleeneAlgebra.assoc
d_assoc_1372 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1372 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.comm
d_comm_1374 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1374 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.∙-cong
d_'8729''45'cong_1376 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1376 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.∙-congʳ
d_'8729''45'cong'691'_1378 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1378 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.∙-congˡ
d_'8729''45'cong'737'_1380 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1380 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.+-idem
d_'43''45'idem_1382 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1382 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.identity
d_identity_1384 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1384 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
                     (coe v0))))))
-- Data.Integer.Properties._.IsKleeneAlgebra.identityʳ
d_identity'691'_1386 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1386 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.identityˡ
d_identity'737'_1388 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1388 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.isBand
d_isBand_1390 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1390 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isBand_1390 v5
du_isBand_1390 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1390 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isBand_876
            (coe
               MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
               (coe v2))))
-- Data.Integer.Properties._.IsKleeneAlgebra.isCommutativeBand
d_isCommutativeBand_1392 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1392 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeBand_1392 v5
du_isCommutativeBand_1392 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_1392 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
         (coe
            MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
            (coe v1)))
-- Data.Integer.Properties._.IsKleeneAlgebra.isCommutativeMagma
d_isCommutativeMagma_1394 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1394 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_1394 v5
du_isCommutativeMagma_1394 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1394 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
                     (coe v4))))))
-- Data.Integer.Properties._.IsKleeneAlgebra.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1396 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1396 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Integer.Properties._.IsKleeneAlgebra.isCommutativeSemigroup
d_isCommutativeSemigroup_1398 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1398 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_1398 v5
du_isCommutativeSemigroup_1398 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1398 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                  (coe v3)))))
-- Data.Integer.Properties._.IsKleeneAlgebra.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_1400 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_1400 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'43''45'isIdempotentCommutativeMonoid_1400 v5
du_'43''45'isIdempotentCommutativeMonoid_1400 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
du_'43''45'isIdempotentCommutativeMonoid_1400 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
         (coe v0))
-- Data.Integer.Properties._.IsKleeneAlgebra.isIdempotentMonoid
d_isIdempotentMonoid_1402 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1402 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isIdempotentMonoid_1402 v5
du_isIdempotentMonoid_1402 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_1402 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
         (coe
            MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
            (coe v1)))
-- Data.Integer.Properties._.IsKleeneAlgebra.isMagma
d_isMagma_1404 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1404 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
                        (coe v0)))))))
-- Data.Integer.Properties._.IsKleeneAlgebra.isMonoid
d_isMonoid_1406 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1406 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
                  (coe v0)))))
-- Data.Integer.Properties._.IsKleeneAlgebra.isSemigroup
d_isSemigroup_1408 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1408 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
                     (coe v0))))))
-- Data.Integer.Properties._.IsKleeneAlgebra.isUnitalMagma
d_isUnitalMagma_1410 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1410 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1410 v5
du_isUnitalMagma_1410 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1410 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v4))))))
-- Data.Integer.Properties._.IsKleeneAlgebra.distrib
d_distrib_1412 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1412 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Integer.Properties._.IsKleeneAlgebra.distribʳ
d_distrib'691'_1414 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1414 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.distribˡ
d_distrib'737'_1416 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1416 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.isEquivalence
d_isEquivalence_1418 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1418 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
                           (coe v0))))))))
-- Data.Integer.Properties._.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_1420 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998
d_isIdempotentSemiring_1420 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
      (coe v0)
-- Data.Integer.Properties._.IsKleeneAlgebra.isNearSemiring
d_isNearSemiring_1422 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_1422 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isNearSemiring_1422 v5
du_isNearSemiring_1422 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_1422 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
            (coe
               MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
               (coe v2))))
-- Data.Integer.Properties._.IsKleeneAlgebra.isPartialEquivalence
d_isPartialEquivalence_1424 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1424 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1424 v5
du_isPartialEquivalence_1424 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1424 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                              (coe v7)))))))))
-- Data.Integer.Properties._.IsKleeneAlgebra.isSemiring
d_isSemiring_1426 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_1426 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
         (coe v0))
-- Data.Integer.Properties._.IsKleeneAlgebra.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1428 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1428 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
            (coe v0)))
-- Data.Integer.Properties._.IsKleeneAlgebra.isSemiringWithoutOne
d_isSemiringWithoutOne_1430 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1430 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isSemiringWithoutOne_1430 v5
du_isSemiringWithoutOne_1430 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1430 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1)))
-- Data.Integer.Properties._.IsKleeneAlgebra.refl
d_refl_1432 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1432 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.reflexive
d_reflexive_1434 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1434 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.setoid
d_setoid_1436 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1436 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_1436 v5
du_setoid_1436 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1436 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_202
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v6))))))))
-- Data.Integer.Properties._.IsKleeneAlgebra.starDestructive
d_starDestructive_1438 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_1438 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_starDestructive_2144 (coe v0)
-- Data.Integer.Properties._.IsKleeneAlgebra.starDestructiveʳ
d_starDestructive'691'_1440 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starDestructive'691'_1440 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.starDestructiveˡ
d_starDestructive'737'_1442 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starDestructive'737'_1442 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.starExpansive
d_starExpansive_1444 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_1444 v0
  = coe MAlonzo.Code.Algebra.Structures.d_starExpansive_2142 (coe v0)
-- Data.Integer.Properties._.IsKleeneAlgebra.starExpansiveʳ
d_starExpansive'691'_1446 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starExpansive'691'_1446 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.starExpansiveˡ
d_starExpansive'737'_1448 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starExpansive'737'_1448 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.sym
d_sym_1450 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1450 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.trans
d_trans_1452 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1452 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.zero
d_zero_1454 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1454 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
            (coe v0)))
-- Data.Integer.Properties._.IsKleeneAlgebra.zeroʳ
d_zero'691'_1456 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1456 = erased
-- Data.Integer.Properties._.IsKleeneAlgebra.zeroˡ
d_zero'737'_1458 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1458 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.//-cong
d_'47''47''45'cong_1462 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1462 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.//-congʳ
d_'47''47''45'cong'691'_1464 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1464 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.//-congˡ
d_'47''47''45'cong'737'_1466 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1466 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.\\-cong
d_'92''92''45'cong_1468 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1468 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.\\-congʳ
d_'92''92''45'cong'691'_1470 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1470 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.\\-congˡ
d_'92''92''45'cong'737'_1472 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1472 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.identity
d_identity_1474 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1474 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))
-- Data.Integer.Properties._.IsLeftBolLoop.identityʳ
d_identity'691'_1476 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1476 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.identityˡ
d_identity'737'_1478 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1478 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.isEquivalence
d_isEquivalence_1480 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1480 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))))
-- Data.Integer.Properties._.IsLeftBolLoop.isLoop
d_isLoop_1482 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1482 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)
-- Data.Integer.Properties._.IsLeftBolLoop.isMagma
d_isMagma_1484 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1484 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Integer.Properties._.IsLeftBolLoop.isPartialEquivalence
d_isPartialEquivalence_1486 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1486 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1486 v4
du_isPartialEquivalence_1486 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1486 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Data.Integer.Properties._.IsLeftBolLoop.isQuasigroup
d_isQuasigroup_1488 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1488 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))
-- Data.Integer.Properties._.IsLeftBolLoop.leftBol
d_leftBol_1490 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1490 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.leftDivides
d_leftDivides_1492 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1492 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Integer.Properties._.IsLeftBolLoop.leftDividesʳ
d_leftDivides'691'_1494 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1494 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.leftDividesˡ
d_leftDivides'737'_1496 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1496 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.refl
d_refl_1498 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1498 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.reflexive
d_reflexive_1500 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1500 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.rightDivides
d_rightDivides_1502 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1502 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Integer.Properties._.IsLeftBolLoop.rightDividesʳ
d_rightDivides'691'_1504 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1504 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.rightDividesˡ
d_rightDivides'737'_1506 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1506 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.setoid
d_setoid_1508 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1508 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1508 v4
du_setoid_1508 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1508 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Integer.Properties._.IsLeftBolLoop.sym
d_sym_1510 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1510 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.trans
d_trans_1512 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1512 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.∙-cong
d_'8729''45'cong_1514 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1514 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.∙-congʳ
d_'8729''45'cong'691'_1516 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1516 = erased
-- Data.Integer.Properties._.IsLeftBolLoop.∙-congˡ
d_'8729''45'cong'737'_1518 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1518 = erased
-- Data.Integer.Properties._.IsLoop.//-cong
d_'47''47''45'cong_1522 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1522 = erased
-- Data.Integer.Properties._.IsLoop.//-congʳ
d_'47''47''45'cong'691'_1524 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1524 = erased
-- Data.Integer.Properties._.IsLoop.//-congˡ
d_'47''47''45'cong'737'_1526 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1526 = erased
-- Data.Integer.Properties._.IsLoop.\\-cong
d_'92''92''45'cong_1528 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1528 = erased
-- Data.Integer.Properties._.IsLoop.\\-congʳ
d_'92''92''45'cong'691'_1530 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1530 = erased
-- Data.Integer.Properties._.IsLoop.\\-congˡ
d_'92''92''45'cong'737'_1532 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1532 = erased
-- Data.Integer.Properties._.IsLoop.identity
d_identity_1534 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1534 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_3138 (coe v0)
-- Data.Integer.Properties._.IsLoop.identityʳ
d_identity'691'_1536 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1536 = erased
-- Data.Integer.Properties._.IsLoop.identityˡ
d_identity'737'_1538 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1538 = erased
-- Data.Integer.Properties._.IsLoop.isEquivalence
d_isEquivalence_1540 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1540 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0)))
-- Data.Integer.Properties._.IsLoop.isMagma
d_isMagma_1542 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Integer.Properties._.IsLoop.isPartialEquivalence
d_isPartialEquivalence_1544 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1544 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1544 v4
du_isPartialEquivalence_1544 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1544 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Integer.Properties._.IsLoop.isQuasigroup
d_isQuasigroup_1546 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1546 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0)
-- Data.Integer.Properties._.IsLoop.leftDivides
d_leftDivides_1548 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1548 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Integer.Properties._.IsLoop.leftDividesʳ
d_leftDivides'691'_1550 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1550 = erased
-- Data.Integer.Properties._.IsLoop.leftDividesˡ
d_leftDivides'737'_1552 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1552 = erased
-- Data.Integer.Properties._.IsLoop.refl
d_refl_1554 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1554 = erased
-- Data.Integer.Properties._.IsLoop.reflexive
d_reflexive_1556 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1556 = erased
-- Data.Integer.Properties._.IsLoop.rightDivides
d_rightDivides_1558 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1558 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Integer.Properties._.IsLoop.rightDividesʳ
d_rightDivides'691'_1560 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1560 = erased
-- Data.Integer.Properties._.IsLoop.rightDividesˡ
d_rightDivides'737'_1562 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1562 = erased
-- Data.Integer.Properties._.IsLoop.setoid
d_setoid_1564 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1564 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1564 v4
du_setoid_1564 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1564 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v1)))
-- Data.Integer.Properties._.IsLoop.sym
d_sym_1566 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1566 = erased
-- Data.Integer.Properties._.IsLoop.trans
d_trans_1568 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1568 = erased
-- Data.Integer.Properties._.IsLoop.∙-cong
d_'8729''45'cong_1570 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1570 = erased
-- Data.Integer.Properties._.IsLoop.∙-congʳ
d_'8729''45'cong'691'_1572 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1572 = erased
-- Data.Integer.Properties._.IsLoop.∙-congˡ
d_'8729''45'cong'737'_1574 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1574 = erased
-- Data.Integer.Properties._.IsMagma.isEquivalence
d_isEquivalence_1578 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1578 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0)
-- Data.Integer.Properties._.IsMagma.isPartialEquivalence
d_isPartialEquivalence_1580 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1580 ~v0 v1
  = du_isPartialEquivalence_1580 v1
du_isPartialEquivalence_1580 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1580 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0))
-- Data.Integer.Properties._.IsMagma.refl
d_refl_1582 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1582 = erased
-- Data.Integer.Properties._.IsMagma.reflexive
d_reflexive_1584 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1584 = erased
-- Data.Integer.Properties._.IsMagma.setoid
d_setoid_1586 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1586 v0 v1
  = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 v1
-- Data.Integer.Properties._.IsMagma.sym
d_sym_1588 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1588 = erased
-- Data.Integer.Properties._.IsMagma.trans
d_trans_1590 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1590 = erased
-- Data.Integer.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1592 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1592 = erased
-- Data.Integer.Properties._.IsMagma.∙-congʳ
d_'8729''45'cong'691'_1594 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1594 = erased
-- Data.Integer.Properties._.IsMagma.∙-congˡ
d_'8729''45'cong'737'_1596 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1596 = erased
-- Data.Integer.Properties._.IsMedialMagma.isEquivalence
d_isEquivalence_1600 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1600 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0))
-- Data.Integer.Properties._.IsMedialMagma.isMagma
d_isMagma_1602 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1602 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0)
-- Data.Integer.Properties._.IsMedialMagma.isPartialEquivalence
d_isPartialEquivalence_1604 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1604 ~v0 v1
  = du_isPartialEquivalence_1604 v1
du_isPartialEquivalence_1604 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1604 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsMedialMagma.medial
d_medial_1606 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_medial_1606 = erased
-- Data.Integer.Properties._.IsMedialMagma.refl
d_refl_1608 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1608 = erased
-- Data.Integer.Properties._.IsMedialMagma.reflexive
d_reflexive_1610 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1610 = erased
-- Data.Integer.Properties._.IsMedialMagma.setoid
d_setoid_1612 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1612 ~v0 v1 = du_setoid_1612 v1
du_setoid_1612 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1612 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0))
-- Data.Integer.Properties._.IsMedialMagma.sym
d_sym_1614 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1614 = erased
-- Data.Integer.Properties._.IsMedialMagma.trans
d_trans_1616 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1616 = erased
-- Data.Integer.Properties._.IsMedialMagma.∙-cong
d_'8729''45'cong_1618 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1618 = erased
-- Data.Integer.Properties._.IsMedialMagma.∙-congʳ
d_'8729''45'cong'691'_1620 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1620 = erased
-- Data.Integer.Properties._.IsMedialMagma.∙-congˡ
d_'8729''45'cong'737'_1622 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1622 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.//-cong
d_'47''47''45'cong_1626 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1626 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.//-congʳ
d_'47''47''45'cong'691'_1628 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1628 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.//-congˡ
d_'47''47''45'cong'737'_1630 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1630 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.\\-cong
d_'92''92''45'cong_1632 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1632 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.\\-congʳ
d_'92''92''45'cong'691'_1634 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1634 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.\\-congˡ
d_'92''92''45'cong'737'_1636 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1636 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.identity
d_identity_1638 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1638 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))
-- Data.Integer.Properties._.IsMiddleBolLoop.identityʳ
d_identity'691'_1640 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1640 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.identityˡ
d_identity'737'_1642 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1642 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.isEquivalence
d_isEquivalence_1644 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1644 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))))
-- Data.Integer.Properties._.IsMiddleBolLoop.isLoop
d_isLoop_1646 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1646 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)
-- Data.Integer.Properties._.IsMiddleBolLoop.isMagma
d_isMagma_1648 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1648 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Integer.Properties._.IsMiddleBolLoop.isPartialEquivalence
d_isPartialEquivalence_1650 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1650 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1650 v4
du_isPartialEquivalence_1650 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1650 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Data.Integer.Properties._.IsMiddleBolLoop.isQuasigroup
d_isQuasigroup_1652 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1652 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))
-- Data.Integer.Properties._.IsMiddleBolLoop.leftDivides
d_leftDivides_1654 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1654 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Integer.Properties._.IsMiddleBolLoop.leftDividesʳ
d_leftDivides'691'_1656 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1656 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.leftDividesˡ
d_leftDivides'737'_1658 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1658 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.middleBol
d_middleBol_1660 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_middleBol_1660 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.refl
d_refl_1662 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1662 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.reflexive
d_reflexive_1664 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1664 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.rightDivides
d_rightDivides_1666 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1666 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Integer.Properties._.IsMiddleBolLoop.rightDividesʳ
d_rightDivides'691'_1668 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1668 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.rightDividesˡ
d_rightDivides'737'_1670 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1670 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.setoid
d_setoid_1672 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1672 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1672 v4
du_setoid_1672 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1672 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Integer.Properties._.IsMiddleBolLoop.sym
d_sym_1674 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1674 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.trans
d_trans_1676 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1676 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.∙-cong
d_'8729''45'cong_1678 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1678 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.∙-congʳ
d_'8729''45'cong'691'_1680 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1680 = erased
-- Data.Integer.Properties._.IsMiddleBolLoop.∙-congˡ
d_'8729''45'cong'737'_1682 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1682 = erased
-- Data.Integer.Properties._.IsMonoid.assoc
d_assoc_1686 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1686 = erased
-- Data.Integer.Properties._.IsMonoid.identity
d_identity_1688 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1688 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_724 (coe v0)
-- Data.Integer.Properties._.IsMonoid.identityʳ
d_identity'691'_1690 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1690 = erased
-- Data.Integer.Properties._.IsMonoid.identityˡ
d_identity'737'_1692 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1692 = erased
-- Data.Integer.Properties._.IsMonoid.isEquivalence
d_isEquivalence_1694 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1694 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)))
-- Data.Integer.Properties._.IsMonoid.isMagma
d_isMagma_1696 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1696 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0))
-- Data.Integer.Properties._.IsMonoid.isPartialEquivalence
d_isPartialEquivalence_1698 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1698 ~v0 ~v1 v2
  = du_isPartialEquivalence_1698 v2
du_isPartialEquivalence_1698 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1698 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Integer.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1700 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1700 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)
-- Data.Integer.Properties._.IsMonoid.isUnitalMagma
d_isUnitalMagma_1702 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1702 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756 v2
-- Data.Integer.Properties._.IsMonoid.refl
d_refl_1704 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1704 = erased
-- Data.Integer.Properties._.IsMonoid.reflexive
d_reflexive_1706 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1706 = erased
-- Data.Integer.Properties._.IsMonoid.setoid
d_setoid_1708 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1708 ~v0 ~v1 v2 = du_setoid_1708 v2
du_setoid_1708 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1708 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Integer.Properties._.IsMonoid.sym
d_sym_1710 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1710 = erased
-- Data.Integer.Properties._.IsMonoid.trans
d_trans_1712 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1712 = erased
-- Data.Integer.Properties._.IsMonoid.∙-cong
d_'8729''45'cong_1714 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1714 = erased
-- Data.Integer.Properties._.IsMonoid.∙-congʳ
d_'8729''45'cong'691'_1716 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1716 = erased
-- Data.Integer.Properties._.IsMonoid.∙-congˡ
d_'8729''45'cong'737'_1718 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1718 = erased
-- Data.Integer.Properties._.IsMoufangLoop.//-cong
d_'47''47''45'cong_1722 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1722 = erased
-- Data.Integer.Properties._.IsMoufangLoop.//-congʳ
d_'47''47''45'cong'691'_1724 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1724 = erased
-- Data.Integer.Properties._.IsMoufangLoop.//-congˡ
d_'47''47''45'cong'737'_1726 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1726 = erased
-- Data.Integer.Properties._.IsMoufangLoop.\\-cong
d_'92''92''45'cong_1728 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1728 = erased
-- Data.Integer.Properties._.IsMoufangLoop.\\-congʳ
d_'92''92''45'cong'691'_1730 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1730 = erased
-- Data.Integer.Properties._.IsMoufangLoop.\\-congˡ
d_'92''92''45'cong'737'_1732 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1732 = erased
-- Data.Integer.Properties._.IsMoufangLoop.identical
d_identical_1734 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identical_1734 = erased
-- Data.Integer.Properties._.IsMoufangLoop.identity
d_identity_1736 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1736 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3216
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)))
-- Data.Integer.Properties._.IsMoufangLoop.identityʳ
d_identity'691'_1738 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1738 = erased
-- Data.Integer.Properties._.IsMoufangLoop.identityˡ
d_identity'737'_1740 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1740 = erased
-- Data.Integer.Properties._.IsMoufangLoop.isEquivalence
d_isEquivalence_1742 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1742 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLoop_3216
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)))))
-- Data.Integer.Properties._.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_1744 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202
d_isLeftBolLoop_1744 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)
-- Data.Integer.Properties._.IsMoufangLoop.isLoop
d_isLoop_1746 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1746 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isLoop_3216
      (coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))
-- Data.Integer.Properties._.IsMoufangLoop.isMagma
d_isMagma_1748 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1748 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Integer.Properties._.IsMoufangLoop.isPartialEquivalence
d_isPartialEquivalence_1750 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1750 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1750 v4
du_isPartialEquivalence_1750 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1750 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))))))
-- Data.Integer.Properties._.IsMoufangLoop.isQuasigroup
d_isQuasigroup_1752 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1752 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3216
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)))
-- Data.Integer.Properties._.IsMoufangLoop.leftBol
d_leftBol_1754 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1754 = erased
-- Data.Integer.Properties._.IsMoufangLoop.leftDivides
d_leftDivides_1756 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1756 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Integer.Properties._.IsMoufangLoop.leftDividesʳ
d_leftDivides'691'_1758 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1758 = erased
-- Data.Integer.Properties._.IsMoufangLoop.leftDividesˡ
d_leftDivides'737'_1760 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1760 = erased
-- Data.Integer.Properties._.IsMoufangLoop.refl
d_refl_1762 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1762 = erased
-- Data.Integer.Properties._.IsMoufangLoop.reflexive
d_reflexive_1764 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1764 = erased
-- Data.Integer.Properties._.IsMoufangLoop.rightBol
d_rightBol_1766 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_1766 = erased
-- Data.Integer.Properties._.IsMoufangLoop.rightDivides
d_rightDivides_1768 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1768 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Integer.Properties._.IsMoufangLoop.rightDividesʳ
d_rightDivides'691'_1770 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1770 = erased
-- Data.Integer.Properties._.IsMoufangLoop.rightDividesˡ
d_rightDivides'737'_1772 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1772 = erased
-- Data.Integer.Properties._.IsMoufangLoop.setoid
d_setoid_1774 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1774 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1774 v4
du_setoid_1774 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1774 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v3)))))
-- Data.Integer.Properties._.IsMoufangLoop.sym
d_sym_1776 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1776 = erased
-- Data.Integer.Properties._.IsMoufangLoop.trans
d_trans_1778 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1778 = erased
-- Data.Integer.Properties._.IsMoufangLoop.∙-cong
d_'8729''45'cong_1780 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1780 = erased
-- Data.Integer.Properties._.IsMoufangLoop.∙-congʳ
d_'8729''45'cong'691'_1782 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1782 = erased
-- Data.Integer.Properties._.IsMoufangLoop.∙-congˡ
d_'8729''45'cong'737'_1784 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1784 = erased
-- Data.Integer.Properties._.IsNearSemiring.*-assoc
d_'42''45'assoc_1788 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1788 = erased
-- Data.Integer.Properties._.IsNearSemiring.*-cong
d_'42''45'cong_1790 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1790 = erased
-- Data.Integer.Properties._.IsNearSemiring.∙-congʳ
d_'8729''45'cong'691'_1792 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1792 = erased
-- Data.Integer.Properties._.IsNearSemiring.∙-congˡ
d_'8729''45'cong'737'_1794 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1794 = erased
-- Data.Integer.Properties._.IsNearSemiring.*-isMagma
d_'42''45'isMagma_1796 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1796 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324 v3
-- Data.Integer.Properties._.IsNearSemiring.*-isSemigroup
d_'42''45'isSemigroup_1798 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1798 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326 v3
-- Data.Integer.Properties._.IsNearSemiring.assoc
d_assoc_1800 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1800 = erased
-- Data.Integer.Properties._.IsNearSemiring.∙-cong
d_'8729''45'cong_1802 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1802 = erased
-- Data.Integer.Properties._.IsNearSemiring.∙-congʳ
d_'8729''45'cong'691'_1804 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1804 = erased
-- Data.Integer.Properties._.IsNearSemiring.∙-congˡ
d_'8729''45'cong'737'_1806 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1806 = erased
-- Data.Integer.Properties._.IsNearSemiring.identity
d_identity_1808 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1808 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Integer.Properties._.IsNearSemiring.identityʳ
d_identity'691'_1810 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1810 = erased
-- Data.Integer.Properties._.IsNearSemiring.identityˡ
d_identity'737'_1812 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1812 = erased
-- Data.Integer.Properties._.IsNearSemiring.isMagma
d_isMagma_1814 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1814 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0)))
-- Data.Integer.Properties._.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1816 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1816 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0)
-- Data.Integer.Properties._.IsNearSemiring.isSemigroup
d_isSemigroup_1818 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1818 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Integer.Properties._.IsNearSemiring.isUnitalMagma
d_isUnitalMagma_1820 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1820 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_1820 v3
du_isUnitalMagma_1820 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1820 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Integer.Properties._.IsNearSemiring.distribʳ
d_distrib'691'_1822 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1822 = erased
-- Data.Integer.Properties._.IsNearSemiring.isEquivalence
d_isEquivalence_1824 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1824 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))))
-- Data.Integer.Properties._.IsNearSemiring.isPartialEquivalence
d_isPartialEquivalence_1826 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1826 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1826 v3
du_isPartialEquivalence_1826 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1826 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278
              (coe v0) in
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
-- Data.Integer.Properties._.IsNearSemiring.refl
d_refl_1828 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1828 = erased
-- Data.Integer.Properties._.IsNearSemiring.reflexive
d_reflexive_1830 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1830 = erased
-- Data.Integer.Properties._.IsNearSemiring.setoid
d_setoid_1832 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1832 ~v0 ~v1 ~v2 v3 = du_setoid_1832 v3
du_setoid_1832 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1832 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Integer.Properties._.IsNearSemiring.sym
d_sym_1834 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1834 = erased
-- Data.Integer.Properties._.IsNearSemiring.trans
d_trans_1836 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1836 = erased
-- Data.Integer.Properties._.IsNearSemiring.zeroˡ
d_zero'737'_1838 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1838 = erased
-- Data.Integer.Properties._.IsNearring.*-assoc
d_'42''45'assoc_1842 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1842 = erased
-- Data.Integer.Properties._.IsNearring.*-cong
d_'42''45'cong_1844 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1844 = erased
-- Data.Integer.Properties._.IsNearring.∙-congʳ
d_'8729''45'cong'691'_1846 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1846 = erased
-- Data.Integer.Properties._.IsNearring.∙-congˡ
d_'8729''45'cong'737'_1848 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1848 = erased
-- Data.Integer.Properties._.IsNearring.*-identity
d_'42''45'identity_1850 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1850 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2288
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Integer.Properties._.IsNearring.identityʳ
d_identity'691'_1852 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1852 = erased
-- Data.Integer.Properties._.IsNearring.identityˡ
d_identity'737'_1854 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1854 = erased
-- Data.Integer.Properties._.IsNearring.*-isMagma
d_'42''45'isMagma_1856 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1856 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMagma_1856 v5
du_'42''45'isMagma_1856 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1856 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2342
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Integer.Properties._.IsNearring.*-isMonoid
d_'42''45'isMonoid_1858 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1858 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMonoid_1858 v5
du_'42''45'isMonoid_1858 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1858 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2346
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Integer.Properties._.IsNearring.*-isSemigroup
d_'42''45'isSemigroup_1860 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1860 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isSemigroup_1860 v5
du_'42''45'isSemigroup_1860 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1860 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_2344
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Integer.Properties._.IsNearring.assoc
d_assoc_1862 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1862 = erased
-- Data.Integer.Properties._.IsNearring.∙-cong
d_'8729''45'cong_1864 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1864 = erased
-- Data.Integer.Properties._.IsNearring.∙-congʳ
d_'8729''45'cong'691'_1866 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1866 = erased
-- Data.Integer.Properties._.IsNearring.∙-congˡ
d_'8729''45'cong'737'_1868 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1868 = erased
-- Data.Integer.Properties._.IsNearring.identity
d_identity_1870 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1870 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))
-- Data.Integer.Properties._.IsNearring.identityʳ
d_identity'691'_1872 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1872 = erased
-- Data.Integer.Properties._.IsNearring.identityˡ
d_identity'737'_1874 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1874 = erased
-- Data.Integer.Properties._.IsNearring.+-inverse
d_'43''45'inverse_1876 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_1876 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'inverse_2646 (coe v0)
-- Data.Integer.Properties._.IsNearring.+-inverseʳ
d_'43''45'inverse'691'_1878 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'691'_1878 = erased
-- Data.Integer.Properties._.IsNearring.+-inverseˡ
d_'43''45'inverse'737'_1880 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'737'_1880 = erased
-- Data.Integer.Properties._.IsNearring.isMagma
d_isMagma_1882 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1882 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
            (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))))
-- Data.Integer.Properties._.IsNearring.+-isMonoid
d_'43''45'isMonoid_1884 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1884 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Integer.Properties._.IsNearring.isSemigroup
d_isSemigroup_1886 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1886 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))
-- Data.Integer.Properties._.IsNearring.isUnitalMagma
d_isUnitalMagma_1888 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1888 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1888 v5
du_isUnitalMagma_1888 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1888 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v1)))
-- Data.Integer.Properties._.IsNearring.distrib
d_distrib_1890 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1890 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2290
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Integer.Properties._.IsNearring.distribʳ
d_distrib'691'_1892 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1892 = erased
-- Data.Integer.Properties._.IsNearring.distribˡ
d_distrib'737'_1894 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1894 = erased
-- Data.Integer.Properties._.IsNearring.identityʳ
d_identity'691'_1896 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1896 = erased
-- Data.Integer.Properties._.IsNearring.identityˡ
d_identity'737'_1898 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1898 = erased
-- Data.Integer.Properties._.IsNearring.isEquivalence
d_isEquivalence_1900 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1900 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))))
-- Data.Integer.Properties._.IsNearring.isPartialEquivalence
d_isPartialEquivalence_1902 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1902 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1902 v5
du_isPartialEquivalence_1902 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1902 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
                 (coe v1) in
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
-- Data.Integer.Properties._.IsNearring.isQuasiring
d_isQuasiring_1904 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260
d_isQuasiring_1904 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)
-- Data.Integer.Properties._.IsNearring.refl
d_refl_1906 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1906 = erased
-- Data.Integer.Properties._.IsNearring.reflexive
d_reflexive_1908 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1908 = erased
-- Data.Integer.Properties._.IsNearring.setoid
d_setoid_1910 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1910 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_1910 v5
du_setoid_1910 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1910 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Data.Integer.Properties._.IsNearring.sym
d_sym_1912 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1912 = erased
-- Data.Integer.Properties._.IsNearring.trans
d_trans_1914 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1914 = erased
-- Data.Integer.Properties._.IsNearring.zero
d_zero_1916 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1916 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_2292
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Integer.Properties._.IsNearring.zeroʳ
d_zero'691'_1918 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1918 = erased
-- Data.Integer.Properties._.IsNearring.zeroˡ
d_zero'737'_1920 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1920 = erased
-- Data.Integer.Properties._.IsNearring.⁻¹-cong
d_'8315''185''45'cong_1922 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1922 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing._//_
d__'47''47'__1926 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> Integer -> Integer
d__'47''47'__1926 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__1926 v0 v2
du__'47''47'__1926 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__1926 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Integer.Properties._.IsNonAssociativeRing.*-cong
d_'42''45'cong_1928 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1928 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.∙-congʳ
d_'8729''45'cong'691'_1930 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1930 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.∙-congˡ
d_'8729''45'cong'737'_1932 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1932 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.*-identity
d_'42''45'identity_1934 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1934 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2520 (coe v0)
-- Data.Integer.Properties._.IsNonAssociativeRing.*-identityʳ
d_'42''45'identity'691'_1936 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_1936 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.*-identityˡ
d_'42''45'identity'737'_1938 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_1938 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.*-isMagma
d_'42''45'isMagma_1940 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1940 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2600 v5
-- Data.Integer.Properties._.IsNonAssociativeRing.*-isUnitalMagma
d_'42''45'isUnitalMagma_1942 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_'42''45'isUnitalMagma_1942 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isUnitalMagma_2606 v5
-- Data.Integer.Properties._.IsNonAssociativeRing.assoc
d_assoc_1944 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1944 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.comm
d_comm_1946 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1946 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.∙-cong
d_'8729''45'cong_1948 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1948 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.∙-congʳ
d_'8729''45'cong'691'_1950 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1950 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.∙-congˡ
d_'8729''45'cong'737'_1952 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1952 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.identity
d_identity_1954 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1954 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
               (coe v0))))
-- Data.Integer.Properties._.IsNonAssociativeRing.identityʳ
d_identity'691'_1956 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1956 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.identityˡ
d_identity'737'_1958 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1958 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_1960 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_1960 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
      (coe v0)
-- Data.Integer.Properties._.IsNonAssociativeRing.isCommutativeMagma
d_isCommutativeMagma_1962 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1962 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_1962 v5
du_isCommutativeMagma_1962 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1962 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
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
-- Data.Integer.Properties._.IsNonAssociativeRing.isCommutativeMonoid
d_isCommutativeMonoid_1964 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_1964 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_1964 v5
du_isCommutativeMonoid_1964 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_1964 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
         (coe v0))
-- Data.Integer.Properties._.IsNonAssociativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_1966 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1966 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_1966 v5
du_isCommutativeSemigroup_1966 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1966 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
            (coe v1)))
-- Data.Integer.Properties._.IsNonAssociativeRing.isGroup
d_isGroup_1968 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_1968 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
         (coe v0))
-- Data.Integer.Properties._.IsNonAssociativeRing.isInvertibleMagma
d_isInvertibleMagma_1970 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1970 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_1970 v5
du_isInvertibleMagma_1970 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_1970 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Integer.Properties._.IsNonAssociativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1972 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_1972 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_1972 v5
du_isInvertibleUnitalMagma_1972 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_1972 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Integer.Properties._.IsNonAssociativeRing.isMagma
d_isMagma_1974 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1974 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
                  (coe v0)))))
-- Data.Integer.Properties._.IsNonAssociativeRing.isMonoid
d_isMonoid_1976 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1976 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
            (coe v0)))
-- Data.Integer.Properties._.IsNonAssociativeRing.isSemigroup
d_isSemigroup_1978 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1978 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
               (coe v0))))
-- Data.Integer.Properties._.IsNonAssociativeRing.isUnitalMagma
d_isUnitalMagma_1980 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1980 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1980 v5
du_isUnitalMagma_1980 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1980 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2))))
-- Data.Integer.Properties._.IsNonAssociativeRing.⁻¹-cong
d_'8315''185''45'cong_1982 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1982 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.inverse
d_inverse_1984 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1984 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
            (coe v0)))
-- Data.Integer.Properties._.IsNonAssociativeRing.inverseʳ
d_inverse'691'_1986 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1986 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.inverseˡ
d_inverse'737'_1988 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1988 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.distrib
d_distrib_1990 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1990 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2522 (coe v0)
-- Data.Integer.Properties._.IsNonAssociativeRing.distribʳ
d_distrib'691'_1992 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1992 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.distribˡ
d_distrib'737'_1994 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1994 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.isEquivalence
d_isEquivalence_1996 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1996 v0
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
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
                     (coe v0))))))
-- Data.Integer.Properties._.IsNonAssociativeRing.isPartialEquivalence
d_isPartialEquivalence_1998 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1998 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1998 v5
du_isPartialEquivalence_1998 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1998 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
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
-- Data.Integer.Properties._.IsNonAssociativeRing.refl
d_refl_2000 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2000 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.reflexive
d_reflexive_2002 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2002 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.setoid
d_setoid_2004 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2004 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_2004 v5
du_setoid_2004 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2004 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
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
-- Data.Integer.Properties._.IsNonAssociativeRing.sym
d_sym_2006 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2006 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.trans
d_trans_2008 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2008 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2010 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2010 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2012 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2012 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.zero
d_zero_2014 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2014 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2524 (coe v0)
-- Data.Integer.Properties._.IsNonAssociativeRing.zeroʳ
d_zero'691'_2016 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2016 = erased
-- Data.Integer.Properties._.IsNonAssociativeRing.zeroˡ
d_zero'737'_2018 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2018 = erased
-- Data.Integer.Properties._.IsQuasigroup.//-cong
d_'47''47''45'cong_2022 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2022 = erased
-- Data.Integer.Properties._.IsQuasigroup.//-congʳ
d_'47''47''45'cong'691'_2024 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_2024 = erased
-- Data.Integer.Properties._.IsQuasigroup.//-congˡ
d_'47''47''45'cong'737'_2026 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_2026 = erased
-- Data.Integer.Properties._.IsQuasigroup.\\-cong
d_'92''92''45'cong_2028 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2028 = erased
-- Data.Integer.Properties._.IsQuasigroup.\\-congʳ
d_'92''92''45'cong'691'_2030 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_2030 = erased
-- Data.Integer.Properties._.IsQuasigroup.\\-congˡ
d_'92''92''45'cong'737'_2032 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_2032 = erased
-- Data.Integer.Properties._.IsQuasigroup.isEquivalence
d_isEquivalence_2034 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2034 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0))
-- Data.Integer.Properties._.IsQuasigroup.isMagma
d_isMagma_2036 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2036 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0)
-- Data.Integer.Properties._.IsQuasigroup.isPartialEquivalence
d_isPartialEquivalence_2038 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2038 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_2038 v3
du_isPartialEquivalence_2038 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2038 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsQuasigroup.leftDivides
d_leftDivides_2040 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2040 v0
  = coe MAlonzo.Code.Algebra.Structures.d_leftDivides_3062 (coe v0)
-- Data.Integer.Properties._.IsQuasigroup.leftDividesʳ
d_leftDivides'691'_2042 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_2042 = erased
-- Data.Integer.Properties._.IsQuasigroup.leftDividesˡ
d_leftDivides'737'_2044 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_2044 = erased
-- Data.Integer.Properties._.IsQuasigroup.refl
d_refl_2046 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2046 = erased
-- Data.Integer.Properties._.IsQuasigroup.reflexive
d_reflexive_2048 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2048 = erased
-- Data.Integer.Properties._.IsQuasigroup.rightDivides
d_rightDivides_2050 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2050 v0
  = coe MAlonzo.Code.Algebra.Structures.d_rightDivides_3064 (coe v0)
-- Data.Integer.Properties._.IsQuasigroup.rightDividesʳ
d_rightDivides'691'_2052 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_2052 = erased
-- Data.Integer.Properties._.IsQuasigroup.rightDividesˡ
d_rightDivides'737'_2054 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_2054 = erased
-- Data.Integer.Properties._.IsQuasigroup.setoid
d_setoid_2056 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2056 ~v0 ~v1 ~v2 v3 = du_setoid_2056 v3
du_setoid_2056 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2056 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0))
-- Data.Integer.Properties._.IsQuasigroup.sym
d_sym_2058 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2058 = erased
-- Data.Integer.Properties._.IsQuasigroup.trans
d_trans_2060 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2060 = erased
-- Data.Integer.Properties._.IsQuasigroup.∙-cong
d_'8729''45'cong_2062 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2062 = erased
-- Data.Integer.Properties._.IsQuasigroup.∙-congʳ
d_'8729''45'cong'691'_2064 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2064 = erased
-- Data.Integer.Properties._.IsQuasigroup.∙-congˡ
d_'8729''45'cong'737'_2066 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2066 = erased
-- Data.Integer.Properties._.IsQuasiring.*-assoc
d_'42''45'assoc_2070 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2070 = erased
-- Data.Integer.Properties._.IsQuasiring.*-cong
d_'42''45'cong_2072 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2072 = erased
-- Data.Integer.Properties._.IsQuasiring.∙-congʳ
d_'8729''45'cong'691'_2074 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2074 = erased
-- Data.Integer.Properties._.IsQuasiring.∙-congˡ
d_'8729''45'cong'737'_2076 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2076 = erased
-- Data.Integer.Properties._.IsQuasiring.*-identity
d_'42''45'identity_2078 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2078 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2288 (coe v0)
-- Data.Integer.Properties._.IsQuasiring.identityʳ
d_identity'691'_2080 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2080 = erased
-- Data.Integer.Properties._.IsQuasiring.identityˡ
d_identity'737'_2082 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2082 = erased
-- Data.Integer.Properties._.IsQuasiring.*-isMagma
d_'42''45'isMagma_2084 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2084 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2342 v4
-- Data.Integer.Properties._.IsQuasiring.*-isMonoid
d_'42''45'isMonoid_2086 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2086 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2346 v4
-- Data.Integer.Properties._.IsQuasiring.*-isSemigroup
d_'42''45'isSemigroup_2088 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2088 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_2344 v4
-- Data.Integer.Properties._.IsQuasiring.assoc
d_assoc_2090 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2090 = erased
-- Data.Integer.Properties._.IsQuasiring.∙-cong
d_'8729''45'cong_2092 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2092 = erased
-- Data.Integer.Properties._.IsQuasiring.∙-congʳ
d_'8729''45'cong'691'_2094 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2094 = erased
-- Data.Integer.Properties._.IsQuasiring.∙-congˡ
d_'8729''45'cong'737'_2096 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2096 = erased
-- Data.Integer.Properties._.IsQuasiring.identity
d_identity_2098 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2098 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Integer.Properties._.IsQuasiring.identityʳ
d_identity'691'_2100 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2100 = erased
-- Data.Integer.Properties._.IsQuasiring.identityˡ
d_identity'737'_2102 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2102 = erased
-- Data.Integer.Properties._.IsQuasiring.isMagma
d_isMagma_2104 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2104 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0)))
-- Data.Integer.Properties._.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_2106 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_2106 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0)
-- Data.Integer.Properties._.IsQuasiring.isSemigroup
d_isSemigroup_2108 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2108 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Integer.Properties._.IsQuasiring.isUnitalMagma
d_isUnitalMagma_2110 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2110 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2110 v4
du_isUnitalMagma_2110 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2110 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Integer.Properties._.IsQuasiring.distrib
d_distrib_2112 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2112 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2290 (coe v0)
-- Data.Integer.Properties._.IsQuasiring.distribʳ
d_distrib'691'_2114 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2114 = erased
-- Data.Integer.Properties._.IsQuasiring.distribˡ
d_distrib'737'_2116 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2116 = erased
-- Data.Integer.Properties._.IsQuasiring.identityʳ
d_identity'691'_2118 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2118 = erased
-- Data.Integer.Properties._.IsQuasiring.identityˡ
d_identity'737'_2120 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2120 = erased
-- Data.Integer.Properties._.IsQuasiring.isEquivalence
d_isEquivalence_2122 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2122 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))))
-- Data.Integer.Properties._.IsQuasiring.isPartialEquivalence
d_isPartialEquivalence_2124 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2124 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2124 v4
du_isPartialEquivalence_2124 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2124 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
              (coe v0) in
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
-- Data.Integer.Properties._.IsQuasiring.refl
d_refl_2126 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2126 = erased
-- Data.Integer.Properties._.IsQuasiring.reflexive
d_reflexive_2128 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2128 = erased
-- Data.Integer.Properties._.IsQuasiring.setoid
d_setoid_2130 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2130 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2130 v4
du_setoid_2130 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2130 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Integer.Properties._.IsQuasiring.sym
d_sym_2132 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2132 = erased
-- Data.Integer.Properties._.IsQuasiring.trans
d_trans_2134 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2134 = erased
-- Data.Integer.Properties._.IsQuasiring.zero
d_zero_2136 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2136 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2292 (coe v0)
-- Data.Integer.Properties._.IsQuasiring.zeroʳ
d_zero'691'_2138 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2138 = erased
-- Data.Integer.Properties._.IsQuasiring.zeroˡ
d_zero'737'_2140 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2140 = erased
-- Data.Integer.Properties._.IsRightBolLoop.//-cong
d_'47''47''45'cong_2144 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2144 = erased
-- Data.Integer.Properties._.IsRightBolLoop.//-congʳ
d_'47''47''45'cong'691'_2146 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_2146 = erased
-- Data.Integer.Properties._.IsRightBolLoop.//-congˡ
d_'47''47''45'cong'737'_2148 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_2148 = erased
-- Data.Integer.Properties._.IsRightBolLoop.\\-cong
d_'92''92''45'cong_2150 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2150 = erased
-- Data.Integer.Properties._.IsRightBolLoop.\\-congʳ
d_'92''92''45'cong'691'_2152 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_2152 = erased
-- Data.Integer.Properties._.IsRightBolLoop.\\-congˡ
d_'92''92''45'cong'737'_2154 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_2154 = erased
-- Data.Integer.Properties._.IsRightBolLoop.identity
d_identity_2156 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2156 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))
-- Data.Integer.Properties._.IsRightBolLoop.identityʳ
d_identity'691'_2158 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2158 = erased
-- Data.Integer.Properties._.IsRightBolLoop.identityˡ
d_identity'737'_2160 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2160 = erased
-- Data.Integer.Properties._.IsRightBolLoop.isEquivalence
d_isEquivalence_2162 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2162 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))))
-- Data.Integer.Properties._.IsRightBolLoop.isLoop
d_isLoop_2164 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_2164 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)
-- Data.Integer.Properties._.IsRightBolLoop.isMagma
d_isMagma_2166 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2166 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Integer.Properties._.IsRightBolLoop.isPartialEquivalence
d_isPartialEquivalence_2168 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2168 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2168 v4
du_isPartialEquivalence_2168 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2168 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v3)))))
-- Data.Integer.Properties._.IsRightBolLoop.isQuasigroup
d_isQuasigroup_2170 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_2170 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))
-- Data.Integer.Properties._.IsRightBolLoop.leftDivides
d_leftDivides_2172 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2172 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Integer.Properties._.IsRightBolLoop.leftDividesʳ
d_leftDivides'691'_2174 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_2174 = erased
-- Data.Integer.Properties._.IsRightBolLoop.leftDividesˡ
d_leftDivides'737'_2176 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_2176 = erased
-- Data.Integer.Properties._.IsRightBolLoop.refl
d_refl_2178 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2178 = erased
-- Data.Integer.Properties._.IsRightBolLoop.reflexive
d_reflexive_2180 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2180 = erased
-- Data.Integer.Properties._.IsRightBolLoop.rightBol
d_rightBol_2182 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_2182 = erased
-- Data.Integer.Properties._.IsRightBolLoop.rightDivides
d_rightDivides_2184 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2184 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Integer.Properties._.IsRightBolLoop.rightDividesʳ
d_rightDivides'691'_2186 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_2186 = erased
-- Data.Integer.Properties._.IsRightBolLoop.rightDividesˡ
d_rightDivides'737'_2188 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_2188 = erased
-- Data.Integer.Properties._.IsRightBolLoop.setoid
d_setoid_2190 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2190 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2190 v4
du_setoid_2190 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2190 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Integer.Properties._.IsRightBolLoop.sym
d_sym_2192 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2192 = erased
-- Data.Integer.Properties._.IsRightBolLoop.trans
d_trans_2194 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2194 = erased
-- Data.Integer.Properties._.IsRightBolLoop.∙-cong
d_'8729''45'cong_2196 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2196 = erased
-- Data.Integer.Properties._.IsRightBolLoop.∙-congʳ
d_'8729''45'cong'691'_2198 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2198 = erased
-- Data.Integer.Properties._.IsRightBolLoop.∙-congˡ
d_'8729''45'cong'737'_2200 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2200 = erased
-- Data.Integer.Properties._.IsRing._//_
d__'47''47'__2204 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> Integer -> Integer
d__'47''47'__2204 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__2204 v0 v2
du__'47''47'__2204 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__2204 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Integer.Properties._.IsRing.*-assoc
d_'42''45'assoc_2206 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2206 = erased
-- Data.Integer.Properties._.IsRing.*-cong
d_'42''45'cong_2208 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2208 = erased
-- Data.Integer.Properties._.IsRing.∙-congʳ
d_'8729''45'cong'691'_2210 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2210 = erased
-- Data.Integer.Properties._.IsRing.∙-congˡ
d_'8729''45'cong'737'_2212 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2212 = erased
-- Data.Integer.Properties._.IsRing.*-identity
d_'42''45'identity_2214 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2214 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768 (coe v0)
-- Data.Integer.Properties._.IsRing.identityʳ
d_identity'691'_2216 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2216 = erased
-- Data.Integer.Properties._.IsRing.identityˡ
d_identity'737'_2218 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2218 = erased
-- Data.Integer.Properties._.IsRing.*-isMagma
d_'42''45'isMagma_2220 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2220 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMagma_2220 v0 v1 v2 v3 v5
du_'42''45'isMagma_2220 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_2220 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324
         (coe
            MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Data.Integer.Properties._.IsRing.*-isMonoid
d_'42''45'isMonoid_2222 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2222 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2860 v0 v1 v2
      v3 v5
-- Data.Integer.Properties._.IsRing.*-isSemigroup
d_'42''45'isSemigroup_2224 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2224 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isSemigroup_2224 v0 v1 v2 v3 v5
du_'42''45'isSemigroup_2224 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_2224 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326
         (coe
            MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Data.Integer.Properties._.IsRing.assoc
d_assoc_2226 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2226 = erased
-- Data.Integer.Properties._.IsRing.comm
d_comm_2228 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2228 = erased
-- Data.Integer.Properties._.IsRing.∙-cong
d_'8729''45'cong_2230 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2230 = erased
-- Data.Integer.Properties._.IsRing.∙-congʳ
d_'8729''45'cong'691'_2232 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2232 = erased
-- Data.Integer.Properties._.IsRing.∙-congˡ
d_'8729''45'cong'737'_2234 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2234 = erased
-- Data.Integer.Properties._.IsRing.identity
d_identity_2236 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2236 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_2236 v5
du_identity_2236 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2236 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
               (coe v0))))
-- Data.Integer.Properties._.IsRing.identityʳ
d_identity'691'_2238 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2238 = erased
-- Data.Integer.Properties._.IsRing.identityˡ
d_identity'737'_2240 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2240 = erased
-- Data.Integer.Properties._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2242 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2242 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe v0)
-- Data.Integer.Properties._.IsRing.isCommutativeMagma
d_isCommutativeMagma_2244 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2244 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_2244 v5
du_isCommutativeMagma_2244 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2244 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
                  (coe v3)))))
-- Data.Integer.Properties._.IsRing.isCommutativeMonoid
d_isCommutativeMonoid_2246 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2246 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_2246 v5
du_isCommutativeMonoid_2246 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2246 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
            (coe v1)))
-- Data.Integer.Properties._.IsRing.isCommutativeSemigroup
d_isCommutativeSemigroup_2248 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2248 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_2248 v5
du_isCommutativeSemigroup_2248 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2248 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
               (coe v2))))
-- Data.Integer.Properties._.IsRing.isGroup
d_isGroup_2250 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_2250 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_2250 v5
du_isGroup_2250 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
du_isGroup_2250 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
         (coe v0))
-- Data.Integer.Properties._.IsRing.isInvertibleMagma
d_isInvertibleMagma_2252 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_2252 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_2252 v5
du_isInvertibleMagma_2252 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_2252 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v2))))
-- Data.Integer.Properties._.IsRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2254 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2254 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_2254 v5
du_isInvertibleUnitalMagma_2254 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2254 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v2))))
-- Data.Integer.Properties._.IsRing.isMagma
d_isMagma_2256 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2256 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_2256 v5
du_isMagma_2256 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
                  (coe v0)))))
-- Data.Integer.Properties._.IsRing.isMonoid
d_isMonoid_2258 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2258 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_2258 v5
du_isMonoid_2258 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_isMonoid_2258 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v0)))
-- Data.Integer.Properties._.IsRing.isSemigroup
d_isSemigroup_2260 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2260 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_2260 v5
du_isSemigroup_2260 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2260 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
               (coe v0))))
-- Data.Integer.Properties._.IsRing.isUnitalMagma
d_isUnitalMagma_2262 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2262 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_2262 v5
du_isUnitalMagma_2262 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2262 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
               (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v3)))))
-- Data.Integer.Properties._.IsRing.⁻¹-cong
d_'8315''185''45'cong_2264 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2264 = erased
-- Data.Integer.Properties._.IsRing.inverse
d_inverse_2266 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2266 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_2266 v5
du_inverse_2266 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v0)))
-- Data.Integer.Properties._.IsRing.inverseʳ
d_inverse'691'_2268 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_2268 = erased
-- Data.Integer.Properties._.IsRing.inverseˡ
d_inverse'737'_2270 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_2270 = erased
-- Data.Integer.Properties._.IsRing.distrib
d_distrib_2272 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2272 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2770 (coe v0)
-- Data.Integer.Properties._.IsRing.distribʳ
d_distrib'691'_2274 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2274 = erased
-- Data.Integer.Properties._.IsRing.distribˡ
d_distrib'737'_2276 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2276 = erased
-- Data.Integer.Properties._.IsRing.isEquivalence
d_isEquivalence_2278 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2278 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_2278 v5
du_isEquivalence_2278 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2278 v0
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
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
                     (coe v0))))))
-- Data.Integer.Properties._.IsRing.isNearSemiring
d_isNearSemiring_2280 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2280 v0 v1 v2 v3 ~v4 v5
  = du_isNearSemiring_2280 v0 v1 v2 v3 v5
du_isNearSemiring_2280 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_2280 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v4))
-- Data.Integer.Properties._.IsRing.isPartialEquivalence
d_isPartialEquivalence_2282 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2282 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_2282 v5
du_isPartialEquivalence_2282 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2282 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v4) in
                coe
                  (let v6 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v6))))))))
-- Data.Integer.Properties._.IsRing.isRingWithoutOne
d_isRingWithoutOne_2284 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
d_isRingWithoutOne_2284 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 v5
-- Data.Integer.Properties._.IsRing.isSemiring
d_isSemiring_2286 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_2286 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 v0 v1 v2 v3 v5
-- Data.Integer.Properties._.IsRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2288 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2288 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2868
      v5
-- Data.Integer.Properties._.IsRing.isSemiringWithoutOne
d_isSemiringWithoutOne_2290 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2290 v0 v1 v2 v3 ~v4 v5
  = du_isSemiringWithoutOne_2290 v0 v1 v2 v3 v5
du_isSemiringWithoutOne_2290 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2290 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Integer.Properties._.IsRing.refl
d_refl_2292 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2292 = erased
-- Data.Integer.Properties._.IsRing.reflexive
d_reflexive_2294 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2294 = erased
-- Data.Integer.Properties._.IsRing.setoid
d_setoid_2296 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2296 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_2296 v5
du_setoid_2296 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2296 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_202
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v5)))))))
-- Data.Integer.Properties._.IsRing.sym
d_sym_2298 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2298 = erased
-- Data.Integer.Properties._.IsRing.trans
d_trans_2300 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2300 = erased
-- Data.Integer.Properties._.IsRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2302 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2302 = erased
-- Data.Integer.Properties._.IsRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2304 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2304 = erased
-- Data.Integer.Properties._.IsRing.zero
d_zero_2306 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2306 v0 v1 v2 v3 ~v4 v5 = du_zero_2306 v0 v1 v2 v3 v5
du_zero_2306 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2306 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_zero_2468 (coe v0) (coe v1)
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v4))
-- Data.Integer.Properties._.IsRing.zeroʳ
d_zero'691'_2308 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2308 = erased
-- Data.Integer.Properties._.IsRing.zeroˡ
d_zero'737'_2310 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2310 = erased
-- Data.Integer.Properties._.IsRingWithoutOne._//_
d__'47''47'__2314 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> Integer -> Integer
d__'47''47'__2314 v0 ~v1 v2 ~v3 ~v4 = du__'47''47'__2314 v0 v2
du__'47''47'__2314 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__2314 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Integer.Properties._.IsRingWithoutOne.*-assoc
d_'42''45'assoc_2316 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2316 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.*-cong
d_'42''45'cong_2318 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2318 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2320 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2320 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2322 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2322 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.*-isMagma
d_'42''45'isMagma_2324 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2324 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Integer.Properties._.IsRingWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2326 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2326 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Integer.Properties._.IsRingWithoutOne.assoc
d_assoc_2328 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2328 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.comm
d_comm_2330 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2330 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.∙-cong
d_'8729''45'cong_2332 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2332 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2334 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2334 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2336 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2336 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.identity
d_identity_2338 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2338 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
               (coe v0))))
-- Data.Integer.Properties._.IsRingWithoutOne.identityʳ
d_identity'691'_2340 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2340 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.identityˡ
d_identity'737'_2342 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2342 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2344 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2344 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
      (coe v0)
-- Data.Integer.Properties._.IsRingWithoutOne.isCommutativeMagma
d_isCommutativeMagma_2346 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2346 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2346 v4
du_isCommutativeMagma_2346 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2346 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
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
-- Data.Integer.Properties._.IsRingWithoutOne.isCommutativeMonoid
d_isCommutativeMonoid_2348 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2348 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMonoid_2348 v4
du_isCommutativeMonoid_2348 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2348 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
         (coe v0))
-- Data.Integer.Properties._.IsRingWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_2350 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2350 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2350 v4
du_isCommutativeSemigroup_2350 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2350 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
            (coe v1)))
-- Data.Integer.Properties._.IsRingWithoutOne.isGroup
d_isGroup_2352 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_2352 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
         (coe v0))
-- Data.Integer.Properties._.IsRingWithoutOne.isInvertibleMagma
d_isInvertibleMagma_2354 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_2354 ~v0 ~v1 ~v2 ~v3 v4
  = du_isInvertibleMagma_2354 v4
du_isInvertibleMagma_2354 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_2354 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Integer.Properties._.IsRingWithoutOne.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2356 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2356 ~v0 ~v1 ~v2 ~v3 v4
  = du_isInvertibleUnitalMagma_2356 v4
du_isInvertibleUnitalMagma_2356 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2356 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Integer.Properties._.IsRingWithoutOne.isMagma
d_isMagma_2358 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2358 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                  (coe v0)))))
-- Data.Integer.Properties._.IsRingWithoutOne.isMonoid
d_isMonoid_2360 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2360 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
            (coe v0)))
-- Data.Integer.Properties._.IsRingWithoutOne.isSemigroup
d_isSemigroup_2362 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2362 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
               (coe v0))))
-- Data.Integer.Properties._.IsRingWithoutOne.isUnitalMagma
d_isUnitalMagma_2364 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2364 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2364 v4
du_isUnitalMagma_2364 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2364 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v2))))
-- Data.Integer.Properties._.IsRingWithoutOne.⁻¹-cong
d_'8315''185''45'cong_2366 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2366 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.inverse
d_inverse_2368 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2368 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
            (coe v0)))
-- Data.Integer.Properties._.IsRingWithoutOne.inverseʳ
d_inverse'691'_2370 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_2370 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.inverseˡ
d_inverse'737'_2372 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_2372 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.distrib
d_distrib_2374 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2374 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2392 (coe v0)
-- Data.Integer.Properties._.IsRingWithoutOne.distribʳ
d_distrib'691'_2376 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2376 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.distribˡ
d_distrib'737'_2378 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2378 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.isEquivalence
d_isEquivalence_2380 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2380 v0
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
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
                     (coe v0))))))
-- Data.Integer.Properties._.IsRingWithoutOne.isNearSemiring
d_isNearSemiring_2382 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2382
  = coe MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470
-- Data.Integer.Properties._.IsRingWithoutOne.isPartialEquivalence
d_isPartialEquivalence_2384 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2384 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2384 v4
du_isPartialEquivalence_2384 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2384 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
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
-- Data.Integer.Properties._.IsRingWithoutOne.refl
d_refl_2386 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2386 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.reflexive
d_reflexive_2388 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2388 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.setoid
d_setoid_2390 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2390 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2390 v4
du_setoid_2390 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2390 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
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
-- Data.Integer.Properties._.IsRingWithoutOne.sym
d_sym_2392 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2392 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.trans
d_trans_2394 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2394 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2396 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2396 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2398 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2398 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.zero
d_zero_2400 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2400 = coe MAlonzo.Code.Algebra.Structures.du_zero_2468
-- Data.Integer.Properties._.IsRingWithoutOne.zeroʳ
d_zero'691'_2402 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2402 = erased
-- Data.Integer.Properties._.IsRingWithoutOne.zeroˡ
d_zero'737'_2404 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2404 = erased
-- Data.Integer.Properties._.IsSelectiveMagma.isEquivalence
d_isEquivalence_2408 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2408 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0))
-- Data.Integer.Properties._.IsSelectiveMagma.isMagma
d_isMagma_2410 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2410 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0)
-- Data.Integer.Properties._.IsSelectiveMagma.isPartialEquivalence
d_isPartialEquivalence_2412 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2412 ~v0 v1
  = du_isPartialEquivalence_2412 v1
du_isPartialEquivalence_2412 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2412 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsSelectiveMagma.refl
d_refl_2414 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2414 = erased
-- Data.Integer.Properties._.IsSelectiveMagma.reflexive
d_reflexive_2416 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2416 = erased
-- Data.Integer.Properties._.IsSelectiveMagma.sel
d_sel_2418 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_2418 v0
  = coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0)
-- Data.Integer.Properties._.IsSelectiveMagma.setoid
d_setoid_2420 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2420 ~v0 v1 = du_setoid_2420 v1
du_setoid_2420 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2420 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0))
-- Data.Integer.Properties._.IsSelectiveMagma.sym
d_sym_2422 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2422 = erased
-- Data.Integer.Properties._.IsSelectiveMagma.trans
d_trans_2424 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2424 = erased
-- Data.Integer.Properties._.IsSelectiveMagma.∙-cong
d_'8729''45'cong_2426 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2426 = erased
-- Data.Integer.Properties._.IsSelectiveMagma.∙-congʳ
d_'8729''45'cong'691'_2428 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2428 = erased
-- Data.Integer.Properties._.IsSelectiveMagma.∙-congˡ
d_'8729''45'cong'737'_2430 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2430 = erased
-- Data.Integer.Properties._.IsSemigroup.assoc
d_assoc_2434 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2434 = erased
-- Data.Integer.Properties._.IsSemigroup.isEquivalence
d_isEquivalence_2436 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2436 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0))
-- Data.Integer.Properties._.IsSemigroup.isMagma
d_isMagma_2438 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2438 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Data.Integer.Properties._.IsSemigroup.isPartialEquivalence
d_isPartialEquivalence_2440 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2440 ~v0 v1
  = du_isPartialEquivalence_2440 v1
du_isPartialEquivalence_2440 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2440 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsSemigroup.refl
d_refl_2442 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2442 = erased
-- Data.Integer.Properties._.IsSemigroup.reflexive
d_reflexive_2444 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2444 = erased
-- Data.Integer.Properties._.IsSemigroup.setoid
d_setoid_2446 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2446 ~v0 v1 = du_setoid_2446 v1
du_setoid_2446 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2446 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0))
-- Data.Integer.Properties._.IsSemigroup.sym
d_sym_2448 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2448 = erased
-- Data.Integer.Properties._.IsSemigroup.trans
d_trans_2450 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2450 = erased
-- Data.Integer.Properties._.IsSemigroup.∙-cong
d_'8729''45'cong_2452 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2452 = erased
-- Data.Integer.Properties._.IsSemigroup.∙-congʳ
d_'8729''45'cong'691'_2454 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2454 = erased
-- Data.Integer.Properties._.IsSemigroup.∙-congˡ
d_'8729''45'cong'737'_2456 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2456 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.isEquivalence
d_isEquivalence_2460 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2460 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0))
-- Data.Integer.Properties._.IsSemimedialMagma.isMagma
d_isMagma_2462 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2462 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0)
-- Data.Integer.Properties._.IsSemimedialMagma.isPartialEquivalence
d_isPartialEquivalence_2464 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2464 ~v0 v1
  = du_isPartialEquivalence_2464 v1
du_isPartialEquivalence_2464 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2464 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsSemimedialMagma.refl
d_refl_2466 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2466 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.reflexive
d_reflexive_2468 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2468 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.semiMedial
d_semiMedial_2470 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_2470 v0
  = coe MAlonzo.Code.Algebra.Structures.d_semiMedial_418 (coe v0)
-- Data.Integer.Properties._.IsSemimedialMagma.semimedialʳ
d_semimedial'691'_2472 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'691'_2472 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.semimedialˡ
d_semimedial'737'_2474 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'737'_2474 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.setoid
d_setoid_2476 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2476 ~v0 v1 = du_setoid_2476 v1
du_setoid_2476 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2476 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0))
-- Data.Integer.Properties._.IsSemimedialMagma.sym
d_sym_2478 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2478 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.trans
d_trans_2480 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2480 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.∙-cong
d_'8729''45'cong_2482 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2482 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.∙-congʳ
d_'8729''45'cong'691'_2484 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2484 = erased
-- Data.Integer.Properties._.IsSemimedialMagma.∙-congˡ
d_'8729''45'cong'737'_2486 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2486 = erased
-- Data.Integer.Properties._.IsSemiring.*-assoc
d_'42''45'assoc_2490 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2490 = erased
-- Data.Integer.Properties._.IsSemiring.*-cong
d_'42''45'cong_2492 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2492 = erased
-- Data.Integer.Properties._.IsSemiring.∙-congʳ
d_'8729''45'cong'691'_2494 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2494 = erased
-- Data.Integer.Properties._.IsSemiring.∙-congˡ
d_'8729''45'cong'737'_2496 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2496 = erased
-- Data.Integer.Properties._.IsSemiring.*-identity
d_'42''45'identity_2498 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2498 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Integer.Properties._.IsSemiring.identityʳ
d_identity'691'_2500 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2500 = erased
-- Data.Integer.Properties._.IsSemiring.identityˡ
d_identity'737'_2502 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2502 = erased
-- Data.Integer.Properties._.IsSemiring.*-isMagma
d_'42''45'isMagma_2504 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2504 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_2504 v4
du_'42''45'isMagma_2504 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_2504 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Integer.Properties._.IsSemiring.*-isMonoid
d_'42''45'isMonoid_2506 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2506 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_2506 v4
du_'42''45'isMonoid_2506 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_2506 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Integer.Properties._.IsSemiring.*-isSemigroup
d_'42''45'isSemigroup_2508 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2508 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_2508 v4
du_'42''45'isSemigroup_2508 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_2508 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Integer.Properties._.IsSemiring.assoc
d_assoc_2510 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2510 = erased
-- Data.Integer.Properties._.IsSemiring.comm
d_comm_2512 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2512 = erased
-- Data.Integer.Properties._.IsSemiring.∙-cong
d_'8729''45'cong_2514 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2514 = erased
-- Data.Integer.Properties._.IsSemiring.∙-congʳ
d_'8729''45'cong'691'_2516 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2516 = erased
-- Data.Integer.Properties._.IsSemiring.∙-congˡ
d_'8729''45'cong'737'_2518 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2518 = erased
-- Data.Integer.Properties._.IsSemiring.identity
d_identity_2520 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2520 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v0))))
-- Data.Integer.Properties._.IsSemiring.identityʳ
d_identity'691'_2522 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2522 = erased
-- Data.Integer.Properties._.IsSemiring.identityˡ
d_identity'737'_2524 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2524 = erased
-- Data.Integer.Properties._.IsSemiring.isCommutativeMagma
d_isCommutativeMagma_2526 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2526 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2526 v4
du_isCommutativeMagma_2526 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2526 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
               (coe v2))))
-- Data.Integer.Properties._.IsSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2528 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2528 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Integer.Properties._.IsSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_2530 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2530 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2530 v4
du_isCommutativeSemigroup_2530 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2530 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v1)))
-- Data.Integer.Properties._.IsSemiring.isMagma
d_isMagma_2532 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2532 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                  (coe v0)))))
-- Data.Integer.Properties._.IsSemiring.isMonoid
d_isMonoid_2534 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2534 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v0)))
-- Data.Integer.Properties._.IsSemiring.isSemigroup
d_isSemigroup_2536 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2536 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v0))))
-- Data.Integer.Properties._.IsSemiring.isUnitalMagma
d_isUnitalMagma_2538 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2538 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2538 v4
du_isUnitalMagma_2538 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2538 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2))))
-- Data.Integer.Properties._.IsSemiring.distrib
d_distrib_2540 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2540 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Integer.Properties._.IsSemiring.distribʳ
d_distrib'691'_2542 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2542 = erased
-- Data.Integer.Properties._.IsSemiring.distribˡ
d_distrib'737'_2544 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2544 = erased
-- Data.Integer.Properties._.IsSemiring.isEquivalence
d_isEquivalence_2546 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2546 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
                     (coe v0))))))
-- Data.Integer.Properties._.IsSemiring.isNearSemiring
d_isNearSemiring_2548 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2548 ~v0 ~v1 ~v2 ~v3 v4
  = du_isNearSemiring_2548 v4
du_isNearSemiring_2548 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_2548 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe v0))
-- Data.Integer.Properties._.IsSemiring.isPartialEquivalence
d_isPartialEquivalence_2550 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2550 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2550 v4
du_isPartialEquivalence_2550 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2550 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2) in
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
-- Data.Integer.Properties._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2552 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2552 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe v0)
-- Data.Integer.Properties._.IsSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_2554 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2554 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730 v4
-- Data.Integer.Properties._.IsSemiring.refl
d_refl_2556 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2556 = erased
-- Data.Integer.Properties._.IsSemiring.reflexive
d_reflexive_2558 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2558 = erased
-- Data.Integer.Properties._.IsSemiring.setoid
d_setoid_2560 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2560 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2560 v4
du_setoid_2560 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2560 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4))))))
-- Data.Integer.Properties._.IsSemiring.sym
d_sym_2562 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2562 = erased
-- Data.Integer.Properties._.IsSemiring.trans
d_trans_2564 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2564 = erased
-- Data.Integer.Properties._.IsSemiring.zero
d_zero_2566 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2566 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1656 (coe v0)
-- Data.Integer.Properties._.IsSemiring.zeroʳ
d_zero'691'_2568 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2568 = erased
-- Data.Integer.Properties._.IsSemiring.zeroˡ
d_zero'737'_2570 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2570 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2574 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2574 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2576 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2576 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congʳ
d_'8729''45'cong'691'_2578 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2578 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congˡ
d_'8729''45'cong'737'_2580 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2580 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2582 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2582 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562 (coe v0)
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.identityʳ
d_identity'691'_2584 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2584 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.identityˡ
d_identity'737'_2586 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2586 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.*-isMagma
d_'42''45'isMagma_2588 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2588 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614 v4
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.*-isMonoid
d_'42''45'isMonoid_2590 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2590 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618 v4
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.*-isSemigroup
d_'42''45'isSemigroup_2592 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2592 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616 v4
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.assoc
d_assoc_2594 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2594 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.comm
d_comm_2596 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2596 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.∙-cong
d_'8729''45'cong_2598 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2598 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congʳ
d_'8729''45'cong'691'_2600 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2600 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congˡ
d_'8729''45'cong'737'_2602 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2602 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.identity
d_identity_2604 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2604 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v0)))
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.identityʳ
d_identity'691'_2606 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2606 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.identityˡ
d_identity'737'_2608 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2608 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.isCommutativeMagma
d_isCommutativeMagma_2610 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2610 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2610 v4
du_isCommutativeMagma_2610 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2610 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2612 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2612 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe v0)
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.isCommutativeSemigroup
d_isCommutativeSemigroup_2614 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2614 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2614 v4
du_isCommutativeSemigroup_2614 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2614 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe v0))
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.isMagma
d_isMagma_2616 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2616 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe v0))))
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.isMonoid
d_isMonoid_2618 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2618 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe v0))
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.isSemigroup
d_isSemigroup_2620 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2620 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v0)))
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.isUnitalMagma
d_isUnitalMagma_2622 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2622 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2622 v4
du_isUnitalMagma_2622 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2622 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2624 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2624 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1564 (coe v0)
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.distribʳ
d_distrib'691'_2626 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2626 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.distribˡ
d_distrib'737'_2628 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2628 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.isEquivalence
d_isEquivalence_2630 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2630 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
                  (coe v0)))))
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.isPartialEquivalence
d_isPartialEquivalence_2632 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2632 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2632 v4
du_isPartialEquivalence_2632 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2632 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
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
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.refl
d_refl_2634 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2634 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.reflexive
d_reflexive_2636 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2636 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.setoid
d_setoid_2638 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2638 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2638 v4
du_setoid_2638 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2638 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
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
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.sym
d_sym_2640 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2640 = erased
-- Data.Integer.Properties._.IsSemiringWithoutAnnihilatingZero.trans
d_trans_2642 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2642 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2646 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2646 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2648 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2648 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2650 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2650 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2652 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2652 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_2654 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2654 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1410 v3
-- Data.Integer.Properties._.IsSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2656 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2656 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1412 v3
-- Data.Integer.Properties._.IsSemiringWithoutOne.assoc
d_assoc_2658 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2658 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.comm
d_comm_2660 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2660 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.∙-cong
d_'8729''45'cong_2662 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2662 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2664 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2664 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2666 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2666 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.identity
d_identity_2668 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2668 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe v0)))
-- Data.Integer.Properties._.IsSemiringWithoutOne.identityʳ
d_identity'691'_2670 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2670 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.identityˡ
d_identity'737'_2672 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2672 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_2674 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2674 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_2674 v3
du_isCommutativeMagma_2674 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2674 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Integer.Properties._.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2676 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2676 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe v0)
-- Data.Integer.Properties._.IsSemiringWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_2678 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2678 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_2678 v3
du_isCommutativeSemigroup_2678 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2678 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe v0))
-- Data.Integer.Properties._.IsSemiringWithoutOne.isMonoid
d_isMonoid_2680 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2680 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe v0))
-- Data.Integer.Properties._.IsSemiringWithoutOne.distrib
d_distrib_2682 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2682 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1366 (coe v0)
-- Data.Integer.Properties._.IsSemiringWithoutOne.distribʳ
d_distrib'691'_2684 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2684 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.distribˡ
d_distrib'737'_2686 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2686 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.isEquivalence
d_isEquivalence_2688 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2688 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
                  (coe v0)))))
-- Data.Integer.Properties._.IsSemiringWithoutOne.isNearSemiring
d_isNearSemiring_2690 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2690 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428 v3
-- Data.Integer.Properties._.IsSemiringWithoutOne.isPartialEquivalence
d_isPartialEquivalence_2692 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2692 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_2692 v3
du_isPartialEquivalence_2692 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2692 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
                     (coe v0))))))
-- Data.Integer.Properties._.IsSemiringWithoutOne.refl
d_refl_2694 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2694 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.reflexive
d_reflexive_2696 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2696 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.setoid
d_setoid_2698 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2698 ~v0 ~v1 ~v2 v3 = du_setoid_2698 v3
du_setoid_2698 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2698 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
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
-- Data.Integer.Properties._.IsSemiringWithoutOne.sym
d_sym_2700 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2700 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.trans
d_trans_2702 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2702 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.zero
d_zero_2704 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2704 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1368 (coe v0)
-- Data.Integer.Properties._.IsSemiringWithoutOne.zeroʳ
d_zero'691'_2706 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2706 = erased
-- Data.Integer.Properties._.IsSemiringWithoutOne.zeroˡ
d_zero'737'_2708 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2708 = erased
-- Data.Integer.Properties._.IsSuccessorSet.isEquivalence
d_isEquivalence_2712 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2712 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_156 (coe v0)
-- Data.Integer.Properties._.IsSuccessorSet.isPartialEquivalence
d_isPartialEquivalence_2714 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2714 ~v0 ~v1 v2
  = du_isPartialEquivalence_2714 v2
du_isPartialEquivalence_2714 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2714 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_156 (coe v0))
-- Data.Integer.Properties._.IsSuccessorSet.refl
d_refl_2716 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2716 = erased
-- Data.Integer.Properties._.IsSuccessorSet.reflexive
d_reflexive_2718 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2718 = erased
-- Data.Integer.Properties._.IsSuccessorSet.setoid
d_setoid_2720 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2720 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_setoid_172 v2
-- Data.Integer.Properties._.IsSuccessorSet.suc#-cong
d_suc'35''45'cong_2722 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'35''45'cong_2722 = erased
-- Data.Integer.Properties._.IsSuccessorSet.sym
d_sym_2724 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2724 = erased
-- Data.Integer.Properties._.IsSuccessorSet.trans
d_trans_2726 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2726 = erased
-- Data.Integer.Properties._.IsUnitalMagma.identity
d_identity_2730 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2730 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_678 (coe v0)
-- Data.Integer.Properties._.IsUnitalMagma.identityʳ
d_identity'691'_2732 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2732 = erased
-- Data.Integer.Properties._.IsUnitalMagma.identityˡ
d_identity'737'_2734 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2734 = erased
-- Data.Integer.Properties._.IsUnitalMagma.isEquivalence
d_isEquivalence_2736 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2736 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0))
-- Data.Integer.Properties._.IsUnitalMagma.isMagma
d_isMagma_2738 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2738 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0)
-- Data.Integer.Properties._.IsUnitalMagma.isPartialEquivalence
d_isPartialEquivalence_2740 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2740 ~v0 ~v1 v2
  = du_isPartialEquivalence_2740 v2
du_isPartialEquivalence_2740 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2740 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Integer.Properties._.IsUnitalMagma.refl
d_refl_2742 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2742 = erased
-- Data.Integer.Properties._.IsUnitalMagma.reflexive
d_reflexive_2744 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2744 = erased
-- Data.Integer.Properties._.IsUnitalMagma.setoid
d_setoid_2746 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2746 ~v0 ~v1 v2 = du_setoid_2746 v2
du_setoid_2746 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2746 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0))
-- Data.Integer.Properties._.IsUnitalMagma.sym
d_sym_2748 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2748 = erased
-- Data.Integer.Properties._.IsUnitalMagma.trans
d_trans_2750 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2750 = erased
-- Data.Integer.Properties._.IsUnitalMagma.∙-cong
d_'8729''45'cong_2752 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2752 = erased
-- Data.Integer.Properties._.IsUnitalMagma.∙-congʳ
d_'8729''45'cong'691'_2754 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2754 = erased
-- Data.Integer.Properties._.IsUnitalMagma.∙-congˡ
d_'8729''45'cong'737'_2756 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2756 = erased
-- Data.Integer.Properties.ℤtoℕ.Homomorphic₀
d_Homomorphic'8320'_2760 ::
  (Integer -> Integer) -> Integer -> Integer -> ()
d_Homomorphic'8320'_2760 = erased
-- Data.Integer.Properties.ℤtoℕ.Homomorphic₁
d_Homomorphic'8321'_2762 ::
  (Integer -> Integer) ->
  (Integer -> Integer) -> (Integer -> Integer) -> ()
d_Homomorphic'8321'_2762 = erased
-- Data.Integer.Properties.ℤtoℕ.Homomorphic₂
d_Homomorphic'8322'_2764 ::
  (Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_Homomorphic'8322'_2764 = erased
-- Data.Integer.Properties.ℤtoℕ.Morphism
d_Morphism_2766 :: ()
d_Morphism_2766 = erased
-- Data.Integer.Properties.ℕtoℤ.Homomorphic₀
d_Homomorphic'8320'_2770 ::
  (Integer -> Integer) -> Integer -> Integer -> ()
d_Homomorphic'8320'_2770 = erased
-- Data.Integer.Properties.ℕtoℤ.Homomorphic₁
d_Homomorphic'8321'_2772 ::
  (Integer -> Integer) ->
  (Integer -> Integer) -> (Integer -> Integer) -> ()
d_Homomorphic'8321'_2772 = erased
-- Data.Integer.Properties.ℕtoℤ.Homomorphic₂
d_Homomorphic'8322'_2774 ::
  (Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_Homomorphic'8322'_2774 = erased
-- Data.Integer.Properties.ℕtoℤ.Morphism
d_Morphism_2776 :: ()
d_Morphism_2776 = erased
-- Data.Integer.Properties.+-injective
d_'43''45'injective_2794 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'injective_2794 = erased
-- Data.Integer.Properties.-[1+-injective
d_'45''91'1'43''45'injective_2796 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45''91'1'43''45'injective_2796 = erased
-- Data.Integer.Properties.+[1+-injective
d_'43''91'1'43''45'injective_2798 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''91'1'43''45'injective_2798 = erased
-- Data.Integer.Properties._≟_
d__'8799'__2800 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__2800 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                  erased erased
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v0) (coe v1))
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
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                          erased erased
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v2)
                             (coe v3))))
-- Data.Integer.Properties.≡-setoid
d_'8801''45'setoid_2818 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_2818
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Integer.Properties.≡-decSetoid
d_'8801''45'decSetoid_2820 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_2820
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__2800)
-- Data.Integer.Properties.drop‿+≤+
d_drop'8255''43''8804''43'_2822 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop'8255''43''8804''43'_2822 ~v0 ~v1 v2
  = du_drop'8255''43''8804''43'_2822 v2
du_drop'8255''43''8804''43'_2822 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_drop'8255''43''8804''43'_2822 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.drop‿-≤-
d_drop'8255''45''8804''45'_2826 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop'8255''45''8804''45'_2826 ~v0 ~v1 v2
  = du_drop'8255''45''8804''45'_2826 v2
du_drop'8255''45''8804''45'_2826 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_drop'8255''45''8804''45'_2826 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.≤-reflexive
d_'8804''45'reflexive_2830 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'reflexive_2830 v0 ~v1 ~v2
  = du_'8804''45'reflexive_2830 v0
du_'8804''45'reflexive_2830 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8804''45'reflexive_2830 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
            (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
      _ -> let v1 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v1)))
-- Data.Integer.Properties.≤-refl
d_'8804''45'refl_2836 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'refl_2836 v0 = coe du_'8804''45'reflexive_2830 (coe v0)
-- Data.Integer.Properties.≤-trans
d_'8804''45'trans_2838 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'trans_2838 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45'trans_2838 v3 v4
du_'8804''45'trans_2838 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8804''45'trans_2838 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v7)
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
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v4)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.≤-antisym
d_'8804''45'antisym_2852 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_2852 = erased
-- Data.Integer.Properties.≤-total
d_'8804''45'total_2862 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_2862 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Sum.Base.du_map_84
                  (coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48)
                  (coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48)
                  (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'total_2928
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
                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'total_2928
                             (coe v3) (coe v2))))
-- Data.Integer.Properties._≤?_
d__'8804''63'__2880 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__2880 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                  (coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48)
                  (coe du_drop'8255''43''8804''43'_2822)
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2920 (coe v0)
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
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                          (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34)
                          (coe du_drop'8255''45''8804''45'_2826)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2920 (coe v3)
                             (coe v2))))
-- Data.Integer.Properties.≤-irrelevant
d_'8804''45'irrelevant_2898 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_2898 = erased
-- Data.Integer.Properties.≤-isPreorder
d_'8804''45'isPreorder_2908 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8804''45'isPreorder_2908
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_2830 v0)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45'trans_2838 v3 v4)
-- Data.Integer.Properties.≤-isTotalPreorder
d_'8804''45'isTotalPreorder_2910 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
d_'8804''45'isTotalPreorder_2910
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_178
      (coe d_'8804''45'isPreorder_2908) (coe d_'8804''45'total_2862)
-- Data.Integer.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_2912 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8804''45'isPartialOrder_2912
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe d_'8804''45'isPreorder_2908) erased
-- Data.Integer.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_2914 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8804''45'isTotalOrder_2914
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe d_'8804''45'isPartialOrder_2912) (coe d_'8804''45'total_2862)
-- Data.Integer.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_2916 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8804''45'isDecTotalOrder_2916
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe d_'8804''45'isTotalOrder_2914) (coe d__'8799'__2800)
      (coe d__'8804''63'__2880)
-- Data.Integer.Properties.≤-preorder
d_'8804''45'preorder_2918 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'8804''45'preorder_2918
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      d_'8804''45'isPreorder_2908
-- Data.Integer.Properties.≤-totalPreorder
d_'8804''45'totalPreorder_2920 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240
d_'8804''45'totalPreorder_2920
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_334
      d_'8804''45'isTotalPreorder_2910
-- Data.Integer.Properties.≤-poset
d_'8804''45'poset_2922 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8804''45'poset_2922
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      d_'8804''45'isPartialOrder_2912
-- Data.Integer.Properties.≤-totalOrder
d_'8804''45'totalOrder_2924 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_'8804''45'totalOrder_2924
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1090
      d_'8804''45'isTotalOrder_2914
-- Data.Integer.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_2926 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_'8804''45'decTotalOrder_2926
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      d_'8804''45'isDecTotalOrder_2916
-- Data.Integer.Properties.≤ᵇ⇒≤
d_'8804''7495''8658''8804'_2928 ::
  Integer ->
  Integer -> AgdaAny -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''7495''8658''8804'_2928 v0 v1 ~v2
  = du_'8804''7495''8658''8804'_2928 v0 v1
du_'8804''7495''8658''8804'_2928 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8804''7495''8658''8804'_2928 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
               (coe v0))
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
             _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v1) in
                  coe
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                          (coe v2)))
-- Data.Integer.Properties.≤⇒≤ᵇ
d_'8804''8658''8804''7495'_2936 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> AgdaAny
d_'8804''8658''8804''7495'_2936 ~v0 ~v1 v2
  = du_'8804''8658''8804''7495'_2936 v2
du_'8804''8658''8804''7495'_2936 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> AgdaAny
du_'8804''8658''8804''7495'_2936 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866
             (coe v3)
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.drop‿+<+
d_drop'8255''43''60''43'_2942 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop'8255''43''60''43'_2942 ~v0 ~v1 v2
  = du_drop'8255''43''60''43'_2942 v2
du_drop'8255''43''60''43'_2942 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_drop'8255''43''60''43'_2942 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.drop‿-<-
d_drop'8255''45''60''45'_2946 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_drop'8255''45''60''45'_2946 ~v0 ~v1 v2
  = du_drop'8255''45''60''45'_2946 v2
du_drop'8255''45''60''45'_2946 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_drop'8255''45''60''45'_2946 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.+≮0
d_'43''8814'0_2950 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''8814'0_2950 = erased
-- Data.Integer.Properties.+≮-
d_'43''8814''45'_2952 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''8814''45'_2952 = erased
-- Data.Integer.Properties.<⇒≤
d_'60''8658''8804'_2954 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'60''8658''8804'_2954 ~v0 ~v1 v2 = du_'60''8658''8804'_2954 v2
du_'60''8658''8804'_2954 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'60''8658''8804'_2954 v0
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v3))
      MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
        -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
      MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v3
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.<⇒≢
d_'60''8658''8802'_2960 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_2960 = erased
-- Data.Integer.Properties.<⇒≱
d_'60''8658''8817'_2966 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_2966 = erased
-- Data.Integer.Properties.≤⇒≯
d_'8804''8658''8815'_2972 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_2972 = erased
-- Data.Integer.Properties.≰⇒>
d_'8816''8658''62'_2982 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8816''8658''62'_2982 v0 v1 ~v2 = du_'8816''8658''62'_2982 v0 v1
du_'8816''8658''62'_2982 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'8816''8658''62'_2982 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_'8816''8658''62'_3032 (coe v0)
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
                             MAlonzo.Code.Data.Nat.Properties.du_'8816''8658''62'_3032 (coe v3)
                             (coe v2))))
-- Data.Integer.Properties.≮⇒≥
d_'8814''8658''8805'_3008 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8814''8658''8805'_3008 v0 v1 ~v2
  = du_'8814''8658''8805'_3008 v0 v1
du_'8814''8658''8805'_3008 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8814''8658''8805'_3008 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_3044
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
                             MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_3044
                             (coe v3) (coe v2))))
-- Data.Integer.Properties.>⇒≰
d_'62''8658''8816'_3034 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''8658''8816'_3034 = erased
-- Data.Integer.Properties.≤∧≢⇒<
d_'8804''8743''8802''8658''60'_3036 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8804''8743''8802''8658''60'_3036 v0 v1 v2 ~v3
  = du_'8804''8743''8802''8658''60'_3036 v0 v1 v2
du_'8804''8743''8802''8658''60'_3036 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'8804''8743''8802''8658''60'_3036 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v5
        -> let v6 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_3060
                   (coe v6) (coe v5)))
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_3060
                (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.≤∧≮⇒≡
d_'8804''8743''8814''8658''8801'_3048 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  (MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8743''8814''8658''8801'_3048 = erased
-- Data.Integer.Properties.<-irrefl
d_'60''45'irrefl_3054 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_3054 = erased
-- Data.Integer.Properties.<-asym
d_'60''45'asym_3060 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_3060 = erased
-- Data.Integer.Properties.≤-<-trans
d_'8804''45''60''45'trans_3066 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8804''45''60''45'trans_3066 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45''60''45'trans_3066 v3 v4
du_'8804''45''60''45'trans_3066 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'8804''45''60''45'trans_3066 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
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
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                       (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.<-≤-trans
d_'60''45''8804''45'trans_3080 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'60''45''8804''45'trans_3080 ~v0 ~v1 ~v2 v3 v4
  = du_'60''45''8804''45'trans_3080 v3 v4
du_'60''45''8804''45'trans_3080 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'60''45''8804''45'trans_3080 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
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
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                       (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.<-trans
d_'60''45'trans_3094 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'60''45'trans_3094 ~v0 ~v1 ~v2 v3 v4
  = du_'60''45'trans_3094 v3 v4
du_'60''45'trans_3094 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'60''45'trans_3094 v0 v1
  = coe
      du_'8804''45''60''45'trans_3066
      (coe du_'60''8658''8804'_2954 (coe v0)) (coe v1)
-- Data.Integer.Properties.<-cmp
d_'60''45'cmp_3100 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_3100 v0 v1
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
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v5 ->
                                             coe
                                               MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                               (coe v3))
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                             (coe eqInt (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
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
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                            (coe v8))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                                            (coe
                                                                               MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2824
                                                                               (coe v3)))
                                                                  else coe
                                                                         seq
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                            (coe v8))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                                            (coe
                                                                               MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_3060
                                                                               (coe v3)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_3044
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
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v4 ->
                                     coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                       (coe v2))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe eqInt (coe v0) (coe v1))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
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
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                    (coe v7))
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2824
                                                                       (coe v2)))
                                                          else coe
                                                                 seq
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                    (coe v7))
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                                    (coe
                                                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_3060
                                                                       (coe v2)
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_3044
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
d__'60''63'__3190 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__3190 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                  (coe MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72)
                  (coe du_drop'8255''43''60''43'_2942)
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v0)
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
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                          (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58)
                          (coe du_drop'8255''45''60''45'_2946)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172 (coe v3)
                             (coe v2))))
-- Data.Integer.Properties.<-irrelevant
d_'60''45'irrelevant_3208 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_3208 = erased
-- Data.Integer.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_3218 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_3218
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_3094 v3 v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4)))
-- Data.Integer.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_3224 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''45'isStrictTotalOrder_3224
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe d_'60''45'isStrictPartialOrder_3218) (coe d_'60''45'cmp_3100)
-- Data.Integer.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_3226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'60''45'strictPartialOrder_3226
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      d_'60''45'isStrictPartialOrder_3218
-- Data.Integer.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_3228 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_'60''45'strictTotalOrder_3228
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      d_'60''45'isStrictTotalOrder_3224
-- Data.Integer.Properties.i≮i
d_i'8814'i_3230 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_i'8814'i_3230 = erased
-- Data.Integer.Properties.>-irrefl
d_'62''45'irrefl_3232 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''45'irrefl_3232 = erased
-- Data.Integer.Properties.≤-Reasoning._._IsRelatedTo_
d__IsRelatedTo__3238 a0 a1 = ()
-- Data.Integer.Properties.≤-Reasoning._._∎
d__'8718'_3240 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_3240
  = let v0 = d_'8804''45'isPreorder_2908 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
            (coe v0)))
-- Data.Integer.Properties.≤-Reasoning._.<-go
d_'60''45'go_3242 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_3242
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_3094 v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45''8804''45'trans_3080 v3 v4)
-- Data.Integer.Properties.≤-Reasoning._.IsEquality
d_IsEquality_3244 a0 a1 a2 = ()
-- Data.Integer.Properties.≤-Reasoning._.IsEquality?
d_IsEquality'63'_3246 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_3246 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
      v2
-- Data.Integer.Properties.≤-Reasoning._.IsStrict
d_IsStrict_3248 a0 a1 a2 = ()
-- Data.Integer.Properties.≤-Reasoning._.IsStrict?
d_IsStrict'63'_3250 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_3250 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
      v2
-- Data.Integer.Properties.≤-Reasoning._.begin_
d_begin__3252 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_begin__3252
  = let v0 = d_'8804''45'isPreorder_2908 in
    coe
      (let v1 = \ v1 v2 v3 -> coe du_'60''8658''8804'_2954 v3 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe v0) (coe v1))))
-- Data.Integer.Properties.≤-Reasoning._.begin-contradiction_
d_begin'45'contradiction__3254 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d_begin'45'contradiction__3254 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__248
-- Data.Integer.Properties.≤-Reasoning._.begin_
d_begin__3256 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__3256 = erased
-- Data.Integer.Properties.≤-Reasoning._.begin_
d_begin__3258 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_begin__3258
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
           (coe v0) v1 v2 v3)
-- Data.Integer.Properties.≤-Reasoning._.eqRelation
d_eqRelation_3260 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_3260
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
-- Data.Integer.Properties.≤-Reasoning._.extractEquality
d_extractEquality_3264 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractEquality_3264 = erased
-- Data.Integer.Properties.≤-Reasoning._.extractStrict
d_extractStrict_3266 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_extractStrict_3266 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
      v2 v3
-- Data.Integer.Properties.≤-Reasoning._.start
d_start_3274 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_start_3274
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
      (coe d_'8804''45'isPreorder_2908)
      (\ v0 v1 v2 -> coe du_'60''8658''8804'_2954 v2)
-- Data.Integer.Properties.≤-Reasoning._.step-<
d_step'45''60'_3276 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_3276
  = let v0 = \ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_3094 v3 v4 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160 in
       coe
         (let v2
                = \ v2 v3 v4 v5 v6 -> coe du_'60''45''8804''45'trans_3080 v5 v6 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe v0) (coe v1) (coe v2)))))
-- Data.Integer.Properties.≤-Reasoning._.step-≡
d_step'45''8801'_3278 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_3278
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Integer.Properties.≤-Reasoning._.step-≡-∣
d_step'45''8801''45''8739'_3280 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_3280 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_3280 v2
du_step'45''8801''45''8739'_3280 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_3280 v0 = coe v0
-- Data.Integer.Properties.≤-Reasoning._.step-≡-⟨
d_step'45''8801''45''10216'_3282 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_3282
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Integer.Properties.≤-Reasoning._.step-≡-⟩
d_step'45''8801''45''10217'_3284 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_3284
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Integer.Properties.≤-Reasoning._.step-≡˘
d_step'45''8801''728'_3286 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_3286
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_454
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Integer.Properties.≤-Reasoning._.step-≤
d_step'45''8804'_3288 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_3288
  = let v0 = d_'8804''45'isPreorder_2908 in
    coe
      (let v1
             = \ v1 v2 v3 v4 v5 -> coe du_'8804''45''60''45'trans_3066 v4 v5 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe v0) (coe v1))))
-- Data.Integer.Properties.≤-Reasoning._.stop
d_stop_3290 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_3290
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
      (coe d_'8804''45'isPreorder_2908)
-- Data.Integer.Properties.≤-Reasoning._.strictRelation
d_strictRelation_3294 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_3294
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
-- Data.Integer.Properties.≤-Reasoning._.≈-go
d_'8776''45'go_3296 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_3296
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
      (coe d_'8804''45'isPreorder_2908)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
-- Data.Integer.Properties.≤-Reasoning._.≡-go
d_'8801''45'go_3298 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_3298 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_3298 v4
du_'8801''45'go_3298 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_3298 v0 = coe v0
-- Data.Integer.Properties.≤-Reasoning._.≤-go
d_'8804''45'go_3300 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_3300
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
      (coe d_'8804''45'isPreorder_2908)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45''60''45'trans_3066 v3 v4)
-- Data.Integer.Properties.positive⁻¹
d_positive'8315''185'_3320 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_positive'8315''185'_3320 ~v0 ~v1 = du_positive'8315''185'_3320
du_positive'8315''185'_3320 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_positive'8315''185'_3320
  = coe
      MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Data.Integer.Properties.negative⁻¹
d_negative'8315''185'_3326 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_170 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_negative'8315''185'_3326 ~v0 ~v1 = du_negative'8315''185'_3326
du_negative'8315''185'_3326 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_negative'8315''185'_3326
  = coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
-- Data.Integer.Properties.nonPositive⁻¹
d_nonPositive'8315''185'_3332 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_nonPositive'8315''185'_3332 v0 ~v1
  = du_nonPositive'8315''185'_3332 v0
du_nonPositive'8315''185'_3332 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_nonPositive'8315''185'_3332 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
-- Data.Integer.Properties.nonNegative⁻¹
d_nonNegative'8315''185'_3338 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_nonNegative'8315''185'_3338 ~v0 ~v1
  = du_nonNegative'8315''185'_3338
du_nonNegative'8315''185'_3338 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_nonNegative'8315''185'_3338
  = coe
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Data.Integer.Properties.negative<positive
d_negative'60'positive_3346 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_170 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_negative'60'positive_3346 ~v0 ~v1 ~v2 ~v3
  = du_negative'60'positive_3346
du_negative'60'positive_3346 ::
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_negative'60'positive_3346
  = coe
      du_'60''45'trans_3094 (coe du_negative'8315''185'_3326)
      (coe du_positive'8315''185'_3320)
-- Data.Integer.Properties.neg-involutive
d_neg'45'involutive_3354 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'involutive_3354 = erased
-- Data.Integer.Properties.neg-injective
d_neg'45'injective_3360 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'injective_3360 = erased
-- Data.Integer.Properties.neg-≤-pos
d_neg'45''8804''45'pos_3376 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_neg'45''8804''45'pos_3376 v0 ~v1
  = du_neg'45''8804''45'pos_3376 v0
du_neg'45''8804''45'pos_3376 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_neg'45''8804''45'pos_3376 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
-- Data.Integer.Properties.neg-mono-≤
d_neg'45'mono'45''8804'_3380 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_neg'45'mono'45''8804'_3380 ~v0 v1 v2
  = du_neg'45'mono'45''8804'_3380 v1 v2
du_neg'45'mono'45''8804'_3380 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_neg'45'mono'45''8804'_3380 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v4
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4)
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe du_neg'45''8804''45'pos_3376 (coe v0)
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe du_neg'45''8804''45'pos_3376 (coe v0)
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.neg-cancel-≤
d_neg'45'cancel'45''8804'_3386 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_neg'45'cancel'45''8804'_3386 v0 v1 v2
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
d_neg'45'mono'45''60'_3410 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_neg'45'mono'45''60'_3410 v0 v1 v2
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
d_neg'45'cancel'45''60'_3424 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_neg'45'cancel'45''60'_3424 v0 v1 v2
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
d_'8739'i'8739''8801'0'8658'i'8801'0_3448 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'i'8739''8801'0'8658'i'8801'0_3448 = erased
-- Data.Integer.Properties.∣-i∣≡∣i∣
d_'8739''45'i'8739''8801''8739'i'8739'_3452 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45'i'8739''8801''8739'i'8739'_3452 = erased
-- Data.Integer.Properties.n⊖n≡0
d_n'8854'n'8801'0_3460 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8854'n'8801'0_3460 = erased
-- Data.Integer.Properties.[1+m]⊖[1+n]≡m⊖n
d_'91'1'43'm'93''8854''91'1'43'n'93''8801'm'8854'n_3478 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'1'43'm'93''8854''91'1'43'n'93''8801'm'8854'n_3478 = erased
-- Data.Integer.Properties.⊖-swap
d_'8854''45'swap_3500 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45'swap_3500 = erased
-- Data.Integer.Properties.⊖-≥
d_'8854''45''8805'_3514 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45''8805'_3514 = erased
-- Data.Integer.Properties.≤-⊖
d_'8804''45''8854'_3542 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45''8854'_3542 = erased
-- Data.Integer.Properties.⊖-≤
d_'8854''45''8804'_3556 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45''8804'_3556 = erased
-- Data.Integer.Properties.⊖-<
d_'8854''45''60'_3592 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45''60'_3592 = erased
-- Data.Integer.Properties.⊖-≰
d_'8854''45''8816'_3594 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8854''45''8816'_3594 = erased
-- Data.Integer.Properties.∣⊖∣-≤
d_'8739''8854''8739''45''8804'_3596 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8854''8739''45''8804'_3596 = erased
-- Data.Integer.Properties.∣⊖∣-<
d_'8739''8854''8739''45''60'_3608 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8854''8739''45''60'_3608 = erased
-- Data.Integer.Properties.∣⊖∣-≰
d_'8739''8854''8739''45''8816'_3620 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8854''8739''45''8816'_3620 = erased
-- Data.Integer.Properties.-m+n≡n⊖m
d_'45'm'43'n'8801'n'8854'm_3626 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45'm'43'n'8801'n'8854'm_3626 = erased
-- Data.Integer.Properties.m-n≡m⊖n
d_m'45'n'8801'm'8854'n_3638 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'45'n'8801'm'8854'n_3638 = erased
-- Data.Integer.Properties.-[n⊖m]≡-m+n
d_'45''91'n'8854'm'93''8801''45'm'43'n_3652 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45''91'n'8854'm'93''8801''45'm'43'n_3652 = erased
-- Data.Integer.Properties.∣m⊖n∣≡∣n⊖m∣
d_'8739'm'8854'n'8739''8801''8739'n'8854'm'8739'_3686 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'8854'n'8739''8801''8739'n'8854'm'8739'_3686 = erased
-- Data.Integer.Properties.+-cancelˡ-⊖
d_'43''45'cancel'737''45''8854'_3702 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'737''45''8854'_3702 = erased
-- Data.Integer.Properties.m⊖n≤m
d_m'8854'n'8804'm_3722 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8854'n'8804'm_3722 v0 v1
  = case coe v1 of
      0 -> coe
             d_'8804''45'refl_2836
             (coe
                MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0)
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
                             (coe d_'8804''45'isPreorder_2908)
                             (\ v4 v5 v6 -> coe du_'60''8658''8804'_2954 v6))
                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0) (coe v1))
                          v0
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                             (\ v4 v5 v6 v7 v8 -> v8)
                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0) (coe v1))
                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v3) (coe v2))
                             v0
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                   (coe d_'8804''45'isPreorder_2908)
                                   (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_3066 v7 v8))
                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v3) (coe v2))
                                v3 v0
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                      (coe d_'8804''45'isPreorder_2908)
                                      (\ v4 v5 v6 v7 v8 ->
                                         coe du_'8804''45''60''45'trans_3066 v7 v8))
                                   v3 v0 v0
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                         (coe d_'8804''45'isPreorder_2908))
                                      (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                                      (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                         (coe v3))))
                                (d_m'8854'n'8804'm_3722 (coe v3) (coe v2)))
                             erased)))
-- Data.Integer.Properties.m⊖n<1+m
d_m'8854'n'60'1'43'm_3740 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_m'8854'n'60'1'43'm_3740 v0 v1
  = coe
      du_'8804''45''60''45'trans_3066
      (coe d_m'8854'n'8804'm_3722 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'60'n'43'm_3748 (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Data.Integer.Properties.m⊖1+n<m
d_m'8854'1'43'n'60'm_3752 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_m'8854'1'43'n'60'm_3752 v0 v1 ~v2
  = du_m'8854'1'43'n'60'm_3752 v0 v1
du_m'8854'1'43'n'60'm_3752 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_m'8854'1'43'n'60'm_3752 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v3 = subInt (coe v1) (coe (1 :: Integer)) in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0) (coe v1))
                   (coe v0)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                      (\ v4 v5 v6 v7 v8 -> v8)
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0) (coe v1))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v2) (coe v3))
                      v0
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                            (\ v4 v5 v6 v7 v8 -> coe du_'60''45'trans_3094 v7 v8)
                            (coe
                               MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                            (\ v4 v5 v6 v7 v8 -> coe du_'60''45''8804''45'trans_3080 v7 v8))
                         (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v2) (coe v3))
                         v0 v0
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe d_'8804''45'isPreorder_2908))
                            (coe v0))
                         (d_m'8854'n'60'1'43'm_3740 (coe v2) (coe v3)))
                      erased)))
-- Data.Integer.Properties.-1+m<n⊖m
d_'45'1'43'm'60'n'8854'm_3768 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'45'1'43'm'60'n'8854'm_3768 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                       (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                          (coe subInt (coe (-1 :: Integer)) (coe v0))
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1) (coe v0))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                (\ v4 v5 v6 v7 v8 -> coe du_'60''45'trans_3094 v7 v8)
                                (coe
                                   MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                (\ v4 v5 v6 v7 v8 -> coe du_'60''45''8804''45'trans_3080 v7 v8))
                             (subInt (coe (-1 :: Integer)) (coe v0))
                             (subInt (coe (0 :: Integer)) (coe v0))
                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1) (coe v0))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                   (\ v4 v5 v6 v7 v8 -> coe du_'60''45'trans_3094 v7 v8)
                                   (coe
                                      MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                   (\ v4 v5 v6 v7 v8 -> coe du_'60''45''8804''45'trans_3080 v7 v8))
                                (subInt (coe (0 :: Integer)) (coe v0))
                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v3) (coe v2))
                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1) (coe v0))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                                   (\ v4 v5 v6 v7 v8 -> v8)
                                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v3) (coe v2))
                                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1) (coe v0))
                                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1) (coe v0))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                         (coe d_'8804''45'isPreorder_2908))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1)
                                         (coe v0)))
                                   erased)
                                (d_'45'1'43'm'60'n'8854'm_3768 (coe v2) (coe v3)))
                             (coe
                                MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                   (coe v0))))))
-- Data.Integer.Properties.-[1+m]≤n⊖m+1
d_'45''91'1'43'm'93''8804'n'8854'm'43'1_3786 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'45''91'1'43'm'93''8804'n'8854'm'43'1_3786 v0 v1
  = case coe v1 of
      0 -> coe
             d_'8804''45'refl_2836 (coe subInt (coe (-1 :: Integer)) (coe v0))
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe d_'8804''45'isPreorder_2908)
                   (\ v3 v4 v5 -> coe du_'60''8658''8804'_2954 v5))
                (subInt (coe (-1 :: Integer)) (coe v0))
                (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                   (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                      (coe d_'8804''45'isPreorder_2908)
                      (\ v3 v4 v5 v6 v7 -> coe du_'8804''45''60''45'trans_3066 v6 v7))
                   (subInt (coe (-1 :: Integer)) (coe v0))
                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v2) (coe v0))
                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                      (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                      (\ v3 v4 v5 v6 v7 -> v7)
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v2) (coe v0))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                         (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                         (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe d_'8804''45'isPreorder_2908))
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1)
                            (coe addInt (coe (1 :: Integer)) (coe v0))))
                      erased)
                   (coe
                      du_'60''8658''8804'_2954
                      (coe d_'45'1'43'm'60'n'8854'm_3768 (coe v0) (coe v2)))))
-- Data.Integer.Properties.-1+m≤n⊖m
d_'45'1'43'm'8804'n'8854'm_3802 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'45'1'43'm'8804'n'8854'm_3802 v0 v1
  = coe
      du_'60''8658''8804'_2954
      (coe d_'45'1'43'm'60'n'8854'm_3768 (coe v0) (coe v1))
-- Data.Integer.Properties.0⊖m≤+
d_0'8854'm'8804''43'_3812 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_0'8854'm'8804''43'_3812 v0 ~v1 = du_0'8854'm'8804''43'_3812 v0
du_0'8854'm'8804''43'_3812 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_0'8854'm'8804''43'_3812 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
-- Data.Integer.Properties.sign-⊖-<
d_sign'45''8854''45''60'_3816 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45''8854''45''60'_3816 = erased
-- Data.Integer.Properties.sign-⊖-≰
d_sign'45''8854''45''8816'_3828 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45''8854''45''8816'_3828 = erased
-- Data.Integer.Properties.⊖-monoʳ-≥-≤
d_'8854''45'mono'691''45''8805''45''8804'_3830 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8854''45'mono'691''45''8805''45''8804'_3830 v0 v1 v2 v3
  = case coe v0 of
      0 -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe du_0'8854'm'8804''43'_3812 (coe v1)
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       seq (coe v3)
                       (coe
                          d_'8804''45'refl_2836
                          (coe
                             MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0))
                             (\ v5 v6 -> v5) (0 :: Integer) (0 :: Integer)))
                _ -> let v5 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                            -> coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                    (coe d_'8804''45'isPreorder_2908)
                                    (\ v7 v8 v9 -> coe du_'60''8658''8804'_2954 v9))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0))
                                    (\ v7 v8 -> v7) v1 (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                    (\ v7 v8 -> v8)
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0)) v1
                                    (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                    (\ v7 v8 v9 v10 v11 -> v11)
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe v0) (coe v1))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe v4) (coe v5))
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v7 v8 -> v8)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0)) v1
                                       (0 :: Integer))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                          (\ v7 v8 v9 v10 v11 -> coe du_'60''45'trans_3094 v10 v11)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                          (\ v7 v8 v9 v10 v11 ->
                                             coe du_'60''45''8804''45'trans_3080 v10 v11))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v4) (coe v5))
                                       v0
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v7 v8 -> v8)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0))
                                          v1 (0 :: Integer))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                             (coe d_'8804''45'isPreorder_2908))
                                          (coe v0))
                                       (d_m'8854'n'60'1'43'm_3740 (coe v4) (coe v5)))
                                    erased)
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                            -> let v9 = subInt (coe v2) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                       (coe d_'8804''45'isPreorder_2908)
                                       (\ v10 v11 v12 -> coe du_'60''8658''8804'_2954 v12))
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0))
                                       (\ v10 v11 -> v10) v1 v2)
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v10 v11 -> v11)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0)) v1
                                       v2)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                       (\ v10 v11 v12 v13 v14 -> v14)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v0) (coe v1))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v4) (coe v5))
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v10 v11 -> v11)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0))
                                          v1 v2)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                             (coe d_'8804''45'isPreorder_2908)
                                             (\ v10 v11 v12 v13 v14 ->
                                                coe du_'8804''45''60''45'trans_3066 v13 v14))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v4) (coe v5))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v4) (coe v9))
                                          (coe
                                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                             (\ v10 v11 -> v11)
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v0))
                                             v1 v2)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                                             (\ v10 v11 v12 v13 v14 -> v14)
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v4) (coe v9))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v0) (coe v2))
                                             (coe
                                                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                (\ v10 v11 -> v11)
                                                (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                   (coe v0))
                                                v1 v2)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                   (coe d_'8804''45'isPreorder_2908))
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                   (coe v0) (coe v2)))
                                             erased)
                                          (d_'8854''45'mono'691''45''8805''45''8804'_3830
                                             (coe v4) (coe v5) (coe v9) (coe v8)))
                                       erased))
                          _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Integer.Properties.⊖-monoˡ-≤
d_'8854''45'mono'737''45''8804'_3858 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8854''45'mono'737''45''8804'_3858 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v3
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                0 -> coe
                       seq (coe v3)
                       (coe
                          d_'8804''45'refl_2836
                          (coe
                             MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                             (\ v5 ->
                                MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v5) (coe v0))
                             (\ v5 v6 -> v5) (0 :: Integer) (0 :: Integer)))
                _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                     coe
                       (case coe v3 of
                          MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                            -> coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                    (coe d_'8804''45'isPreorder_2908)
                                    (\ v7 v8 v9 -> coe du_'60''8658''8804'_2954 v9))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                    (\ v7 ->
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                         (coe v7) (coe v0))
                                    (\ v7 v8 -> v7) (0 :: Integer) v2)
                                 (coe
                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                    (\ v7 v8 -> v8)
                                    (\ v7 ->
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                         (coe v7) (coe v0))
                                    (0 :: Integer) v2)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                       (coe d_'8804''45'isPreorder_2908)
                                       (\ v7 v8 v9 v10 v11 ->
                                          coe du_'8804''45''60''45'trans_3066 v10 v11))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe (0 :: Integer)) (coe v0))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe (0 :: Integer)) (coe v4))
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v7 v8 -> v8)
                                       (\ v7 ->
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                            (coe v7) (coe v0))
                                       (0 :: Integer) v2)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                          (coe d_'8804''45'isPreorder_2908)
                                          (\ v7 v8 v9 v10 v11 ->
                                             coe du_'8804''45''60''45'trans_3066 v10 v11))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe (0 :: Integer)) (coe v4))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v5) (coe v4))
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v7 v8 -> v8)
                                          (\ v7 ->
                                             MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                               (coe v7) (coe v0))
                                          (0 :: Integer) v2)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                                          (\ v7 v8 v9 v10 v11 -> v11)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v5) (coe v4))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v2) (coe v0))
                                          (coe
                                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                             (\ v7 v8 -> v8)
                                             (\ v7 ->
                                                MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                  (coe v7) (coe v0))
                                             (0 :: Integer) v2)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe d_'8804''45'isPreorder_2908))
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v2) (coe v0)))
                                          erased)
                                       (d_'8854''45'mono'737''45''8804'_3858
                                          (coe v4) (coe (0 :: Integer)) (coe v5)
                                          (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                                    (d_'8854''45'mono'691''45''8805''45''8804'_3830
                                       (coe (0 :: Integer)) (coe v0) (coe v4)
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                          (coe v4))))
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                            -> let v9 = subInt (coe v1) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                       (coe d_'8804''45'isPreorder_2908)
                                       (\ v10 v11 v12 -> coe du_'60''8658''8804'_2954 v12))
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                       (\ v10 ->
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                            (coe v10) (coe v0))
                                       (\ v10 v11 -> v10) v1 v2)
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v10 v11 -> v11)
                                       (\ v10 ->
                                          MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                            (coe v10) (coe v0))
                                       v1 v2)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                       (\ v10 v11 v12 v13 v14 -> v14)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v1) (coe v0))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v9) (coe v4))
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v10 v11 -> v11)
                                          (\ v10 ->
                                             MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                               (coe v10) (coe v0))
                                          v1 v2)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                             (coe d_'8804''45'isPreorder_2908)
                                             (\ v10 v11 v12 v13 v14 ->
                                                coe du_'8804''45''60''45'trans_3066 v13 v14))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v9) (coe v4))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v5) (coe v4))
                                          (coe
                                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                             (\ v10 v11 -> v11)
                                             (\ v10 ->
                                                MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                  (coe v10) (coe v0))
                                             v1 v2)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                                             (\ v10 v11 v12 v13 v14 -> v14)
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v5) (coe v4))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v2) (coe v0))
                                             (coe
                                                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                (\ v10 v11 -> v11)
                                                (\ v10 ->
                                                   MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                     (coe v10) (coe v0))
                                                v1 v2)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                   (coe d_'8804''45'isPreorder_2908))
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                   (coe v2) (coe v0)))
                                             erased)
                                          (d_'8854''45'mono'737''45''8804'_3858
                                             (coe v4) (coe v9) (coe v5) (coe v8)))
                                       erased))
                          _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Integer.Properties.⊖-monoʳ->-<
d_'8854''45'mono'691''45''62''45''60'_3884 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8854''45'mono'691''45''62''45''60'_3884 v0 v1 v2 v3
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
                            -> coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0) (coe v1))
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                    (\ v10 v11 v12 v13 v14 -> v14)
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe v0) (coe v1))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe v4) (coe v5))
                                    v0
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                          (\ v10 v11 v12 v13 v14 ->
                                             coe du_'60''45'trans_3094 v13 v14)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                          (\ v10 v11 v12 v13 v14 ->
                                             coe du_'60''45''8804''45'trans_3080 v13 v14))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v4) (coe v5))
                                       v0 v0
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                             (coe d_'8804''45'isPreorder_2908))
                                          (coe v0))
                                       (d_m'8854'n'60'1'43'm_3740 (coe v4) (coe v5)))
                                    erased)
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v11
                            -> let v12 = subInt (coe v2) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0)
                                       (coe v1))
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0)
                                       (coe v2))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                       (\ v13 v14 v15 v16 v17 -> v17)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v0) (coe v1))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v4) (coe subInt (coe v1) (coe (1 :: Integer))))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v0) (coe v2))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                             (\ v13 v14 v15 v16 v17 ->
                                                coe du_'60''45'trans_3094 v16 v17)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                             (\ v13 v14 v15 v16 v17 ->
                                                coe du_'60''45''8804''45'trans_3080 v16 v17))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v4) (coe subInt (coe v1) (coe (1 :: Integer))))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v4) (coe v12))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v0) (coe v2))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                                             (\ v13 v14 v15 v16 v17 -> v17)
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v4) (coe v12))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v0) (coe v2))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v0) (coe v2))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                   (coe d_'8804''45'isPreorder_2908))
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                   (coe v0) (coe v2)))
                                             erased)
                                          (d_'8854''45'mono'691''45''62''45''60'_3884
                                             (coe v4) (coe subInt (coe v1) (coe (1 :: Integer)))
                                             (coe v12)
                                             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v11)))
                                       erased))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Integer.Properties.⊖-monoˡ-<
d_'8854''45'mono'737''45''60'_3908 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'8854''45'mono'737''45''60'_3908 v0 v1 v2 v3
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
                            -> coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                                 (coe subInt (coe (0 :: Integer)) (coe v0))
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v2) (coe v0))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                       (\ v10 v11 v12 v13 v14 -> coe du_'60''45'trans_3094 v13 v14)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                       (\ v10 v11 v12 v13 v14 ->
                                          coe du_'60''45''8804''45'trans_3080 v13 v14))
                                    (subInt (coe (0 :: Integer)) (coe v0))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe v5) (coe v4))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe v2) (coe v0))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                                       (\ v10 v11 v12 v13 v14 -> v14)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v5) (coe v4))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v2) (coe v0))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v2) (coe v0))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                             (coe d_'8804''45'isPreorder_2908))
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v2)
                                             (coe v0)))
                                       erased)
                                    (d_'45'1'43'm'60'n'8854'm_3768 (coe v4) (coe v5)))
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v11
                            -> let v12 = subInt (coe v1) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1)
                                       (coe v0))
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v2)
                                       (coe v0))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                       (\ v13 v14 v15 v16 v17 -> v17)
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v1) (coe v0))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v12) (coe v4))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v2) (coe v0))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                             (\ v13 v14 v15 v16 v17 ->
                                                coe du_'60''45'trans_3094 v16 v17)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                             (\ v13 v14 v15 v16 v17 ->
                                                coe du_'60''45''8804''45'trans_3080 v16 v17))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v12) (coe v4))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe subInt (coe v2) (coe (1 :: Integer))) (coe v4))
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v2) (coe v0))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                                             (\ v13 v14 v15 v16 v17 -> v17)
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe subInt (coe v2) (coe (1 :: Integer))) (coe v4))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v2) (coe v0))
                                             (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                (coe v2) (coe v0))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                   (coe d_'8804''45'isPreorder_2908))
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                                   (coe v2) (coe v0)))
                                             erased)
                                          (d_'8854''45'mono'737''45''60'_3908
                                             (coe v4) (coe v12)
                                             (coe subInt (coe v2) (coe (1 :: Integer)))
                                             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v11)))
                                       erased))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Integer.Properties.0≤i⇒+∣i∣≡i
d_0'8804'i'8658''43''8739'i'8739''8801'i_3932 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8804'i'8658''43''8739'i'8739''8801'i_3932 = erased
-- Data.Integer.Properties.+∣i∣≡i⇒0≤i
d_'43''8739'i'8739''8801'i'8658'0'8804'i_3934 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''8739'i'8739''8801'i'8658'0'8804'i_3934 ~v0 ~v1
  = du_'43''8739'i'8739''8801'i'8658'0'8804'i_3934
du_'43''8739'i'8739''8801'i'8658'0'8804'i_3934 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'43''8739'i'8739''8801'i'8658'0'8804'i_3934
  = coe
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Data.Integer.Properties.+∣i∣≡i⊎+∣i∣≡-i
d_'43''8739'i'8739''8801'i'8846''43''8739'i'8739''8801''45'i_3940 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'43''8739'i'8739''8801'i'8846''43''8739'i'8739''8801''45'i_3940 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Integer.Properties.∣m⊝n∣≤m⊔n
d_'8739'm'8861'n'8739''8804'm'8852'n_3950 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'8861'n'8739''8804'm'8852'n_3950
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Consequences.du_wlog_804
              (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'total_2928)
              (coe (\ v0 v1 v2 -> v2)) in
    coe
      (coe
         v0
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
              (coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                 (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                 (\ v4 v5 v6 ->
                    coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v6))
              (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                 (coe
                    MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1) (coe v2)))
              (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v2))
              (coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                 (\ v4 v5 v6 v7 v8 -> v8)
                 (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1) (coe v2)))
                 (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_'45'__260
                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2 v1)))
                 (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v2))
                 (coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                    (\ v4 v5 v6 v7 v8 -> v8)
                    (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d_'45'__260
                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2 v1)))
                    (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2 v1))
                    (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v2))
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                          (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                          (\ v4 v5 v6 v7 v8 ->
                             coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v7
                               v8))
                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2 v1) v2
                       (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v2))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                             (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                             (\ v4 v5 v6 v7 v8 ->
                                coe
                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                  v7 v8))
                          v2 (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v2))
                          (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v2))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                             (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v1) (coe v2)))
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
                             (coe
                                MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962))
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                                (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4582))
                             (coe v1) (coe v2)))
                       (MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
                          (coe v2) (coe v1)))
                    erased)
                 erased)))
-- Data.Integer.Properties.∣i+j∣≤∣i∣+∣j∣
d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3970 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3970 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe (0 :: Integer))
                      (coe v1))))
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v0) (coe v1)))
            _ -> coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                      (\ v2 v3 v4 ->
                         coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v4))
                   (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v0) (coe v1)))
                   (addInt
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                         (\ v2 v3 v4 v5 v6 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v5
                              v6))
                      (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v0)
                            (coe subInt (coe (0 :: Integer)) (coe v1))))
                      (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                         (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1)))
                      (addInt
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                            (\ v2 v3 v4 v5 v6 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v5
                                 v6))
                         (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                            (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1)))
                         (subInt (coe v0) (coe v1))
                         (addInt
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                            (coe subInt (coe v0) (coe v1)))
                         (MAlonzo.Code.Data.Nat.Properties.d_m'8852'n'8804'm'43'n_4972
                            (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))))
                      (coe
                         d_'8739'm'8861'n'8739''8804'm'8852'n_3950 v0
                         (subInt (coe (0 :: Integer)) (coe v1))))
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                      (\ v2 v3 v4 ->
                         coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v4))
                   (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v0) (coe v1)))
                   (addInt
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                         (\ v2 v3 v4 v5 v6 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v5
                              v6))
                      (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v1)
                            (coe subInt (coe (0 :: Integer)) (coe v0))))
                      (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                         (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0)))
                      (addInt
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                            (\ v2 v3 v4 v5 v6 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v5
                                 v6))
                         (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                            (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0)))
                         (subInt (coe v1) (coe v0))
                         (addInt
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                            (\ v2 v3 v4 v5 v6 -> v6) (subInt (coe v1) (coe v0))
                            (subInt (coe v1) (coe v0))
                            (addInt
                               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                  (coe
                                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                               (coe subInt (coe v1) (coe v0)))
                            erased)
                         (MAlonzo.Code.Data.Nat.Properties.d_m'8852'n'8804'm'43'n_4972
                            (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0))))
                      (coe
                         d_'8739'm'8861'n'8739''8804'm'8852'n_3950 v1
                         (subInt (coe (0 :: Integer)) (coe v0))))
             _ -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe subInt (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1))
-- Data.Integer.Properties.∣i-j∣≤∣i∣+∣j∣
d_'8739'i'45'j'8739''8804''8739'i'8739''43''8739'j'8739'_4008 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'i'45'j'8739''8804''8739'i'8739''43''8739'j'8739'_4008 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
         (\ v2 v3 v4 ->
            coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v4))
      (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1)))
      (addInt
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
            (\ v2 v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v5
                 v6))
         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1)))
         (addInt
            (coe
               MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
         (addInt
            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
            (\ v2 v3 v4 v5 v6 -> v6)
            (addInt
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
            (addInt
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
            (addInt
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
               (coe
                  addInt
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))))
            erased)
         (d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3970
            (coe v0)
            (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))))
-- Data.Integer.Properties.◃-nonZero
d_'9667''45'nonZero_4026 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'9667''45'nonZero_4026 v0 ~v1 ~v2 = du_'9667''45'nonZero_4026 v0
du_'9667''45'nonZero_4026 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_'9667''45'nonZero_4026 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_constructor_120
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Integer.Properties.◃-inverse
d_'9667''45'inverse_4030 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45'inverse_4030 = erased
-- Data.Integer.Properties.◃-cong
d_'9667''45'cong_4036 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45'cong_4036 = erased
-- Data.Integer.Properties.+◃n≡+n
d_'43''9667'n'8801''43'n_4052 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''9667'n'8801''43'n_4052 = erased
-- Data.Integer.Properties.-◃n≡-n
d_'45''9667'n'8801''45'n_4056 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45''9667'n'8801''45'n_4056 = erased
-- Data.Integer.Properties.sign-◃
d_sign'45''9667'_4064 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45''9667'_4064 = erased
-- Data.Integer.Properties.abs-◃
d_abs'45''9667'_4070 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45''9667'_4070 = erased
-- Data.Integer.Properties.signᵢ◃∣i∣≡i
d_sign'7522''9667''8739'i'8739''8801'i_4078 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'7522''9667''8739'i'8739''8801'i_4078 = erased
-- Data.Integer.Properties.sign-cong
d_sign'45'cong_4088 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45'cong_4088 = erased
-- Data.Integer.Properties.sign-cong′
d_sign'45'cong'8242'_4104 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sign'45'cong'8242'_4104 v0 v1 ~v2 ~v3 ~v4
  = du_sign'45'cong'8242'_4104 v0 v1
du_sign'45'cong'8242'_4104 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sign'45'cong'8242'_4104 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> let v2
                 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased in
           coe (coe seq (coe v0) (coe v2))
-- Data.Integer.Properties.abs-cong
d_abs'45'cong_4138 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45'cong_4138 = erased
-- Data.Integer.Properties.∣s◃m∣*∣t◃n∣≡m*n
d_'8739's'9667'm'8739''42''8739't'9667'n'8739''8801'm'42'n_4162 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739's'9667'm'8739''42''8739't'9667'n'8739''8801'm'42'n_4162
  = erased
-- Data.Integer.Properties.+◃-mono-<
d_'43''9667''45'mono'45''60'_4172 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''9667''45'mono'45''60'_4172 v0 ~v1 v2
  = du_'43''9667''45'mono'45''60'_4172 v0 v2
du_'43''9667''45'mono'45''60'_4172 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'43''9667''45'mono'45''60'_4172 v0 v1
  = coe
      seq (coe v0)
      (coe MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v1)
-- Data.Integer.Properties.+◃-cancel-<
d_'43''9667''45'cancel'45''60'_4184 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''9667''45'cancel'45''60'_4184 v0 ~v1 v2
  = du_'43''9667''45'cancel'45''60'_4184 v0 v2
du_'43''9667''45'cancel'45''60'_4184 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''9667''45'cancel'45''60'_4184 v0 v1
  = coe
      seq (coe v0)
      (case coe v1 of
         MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v4 -> coe v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Integer.Properties.neg◃-cancel-<
d_neg'9667''45'cancel'45''60'_4198 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_neg'9667''45'cancel'45''60'_4198 ~v0 v1 v2
  = du_neg'9667''45'cancel'45''60'_4198 v1 v2
du_neg'9667''45'cancel'45''60'_4198 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_neg'9667''45'cancel'45''60'_4198 v0 v1
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
d_'45''9667''60''43''9667'_4214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'45''9667''60''43''9667'_4214 ~v0 v1 ~v2
  = du_'45''9667''60''43''9667'_4214 v1
du_'45''9667''60''43''9667'_4214 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'45''9667''60''43''9667'_4214 v0
  = coe
      seq (coe v0) (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64)
-- Data.Integer.Properties.+◃≮-◃
d_'43''9667''8814''45''9667'_4216 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''9667''8814''45''9667'_4216 = erased
-- Data.Integer.Properties.+-comm
d_'43''45'comm_4220 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_4220 = erased
-- Data.Integer.Properties.+-identityˡ
d_'43''45'identity'737'_4230 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737'_4230 = erased
-- Data.Integer.Properties.+-identityʳ
d_'43''45'identity'691'_4232 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_4232 = erased
-- Data.Integer.Properties.+-identity
d_'43''45'identity_4234 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'identity_4234
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.distribˡ-⊖-+-pos
d_distrib'737''45''8854''45''43''45'pos_4242 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737''45''8854''45''43''45'pos_4242 = erased
-- Data.Integer.Properties.distribˡ-⊖-+-neg
d_distrib'737''45''8854''45''43''45'neg_4262 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737''45''8854''45''43''45'neg_4262 = erased
-- Data.Integer.Properties.distribʳ-⊖-+-pos
d_distrib'691''45''8854''45''43''45'pos_4282 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691''45''8854''45''43''45'pos_4282 = erased
-- Data.Integer.Properties.distribʳ-⊖-+-neg
d_distrib'691''45''8854''45''43''45'neg_4302 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691''45''8854''45''43''45'neg_4302 = erased
-- Data.Integer.Properties.+-assoc
d_'43''45'assoc_4316 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_4316 = erased
-- Data.Integer.Properties.+-inverseˡ
d_'43''45'inverse'737'_4496 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'737'_4496 = erased
-- Data.Integer.Properties.+-inverseʳ
d_'43''45'inverse'691'_4502 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'691'_4502 = erased
-- Data.Integer.Properties.+-inverse
d_'43''45'inverse_4504 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_4504
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.+-isMagma
d_'43''45'isMagma_4506 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'43''45'isMagma_4506
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Integer.Properties.+-isSemigroup
d_'43''45'isSemigroup_4508 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'43''45'isSemigroup_4508
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe d_'43''45'isMagma_4506) erased
-- Data.Integer.Properties.+-isCommutativeSemigroup
d_'43''45'isCommutativeSemigroup_4510 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'43''45'isCommutativeSemigroup_4510
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_608
      (coe d_'43''45'isSemigroup_4508) erased
-- Data.Integer.Properties.+-0-isMonoid
d_'43''45'0'45'isMonoid_4512 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'0'45'isMonoid_4512
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe d_'43''45'isSemigroup_4508) (coe d_'43''45'identity_4234)
-- Data.Integer.Properties.+-0-isCommutativeMonoid
d_'43''45'0'45'isCommutativeMonoid_4514 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'0'45'isCommutativeMonoid_4514
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe d_'43''45'0'45'isMonoid_4512) erased
-- Data.Integer.Properties.+-0-isGroup
d_'43''45'0'45'isGroup_4516 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_'43''45'0'45'isGroup_4516
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1164
      (coe d_'43''45'0'45'isMonoid_4512) (coe d_'43''45'inverse_4504)
      erased
-- Data.Integer.Properties.+-0-isAbelianGroup
d_'43''45'0'45'isAbelianGroup_4518 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'0'45'isAbelianGroup_4518
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1252
      (coe d_'43''45'0'45'isGroup_4516) erased
-- Data.Integer.Properties.+-magma
d_'43''45'magma_4520 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'43''45'magma_4520
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124
      MAlonzo.Code.Data.Integer.Base.d__'43'__284 d_'43''45'isMagma_4506
-- Data.Integer.Properties.+-semigroup
d_'43''45'semigroup_4522 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'43''45'semigroup_4522
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614
      MAlonzo.Code.Data.Integer.Base.d__'43'__284
      d_'43''45'isSemigroup_4508
-- Data.Integer.Properties.+-commutativeSemigroup
d_'43''45'commutativeSemigroup_4524 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'43''45'commutativeSemigroup_4524
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_754
      MAlonzo.Code.Data.Integer.Base.d__'43'__284
      d_'43''45'isCommutativeSemigroup_4510
-- Data.Integer.Properties.+-0-monoid
d_'43''45'0'45'monoid_4526 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'43''45'0'45'monoid_4526
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990
      MAlonzo.Code.Data.Integer.Base.d__'43'__284 (0 :: Integer)
      d_'43''45'0'45'isMonoid_4512
-- Data.Integer.Properties.+-0-commutativeMonoid
d_'43''45'0'45'commutativeMonoid_4528 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'43''45'0'45'commutativeMonoid_4528
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088
      MAlonzo.Code.Data.Integer.Base.d__'43'__284 (0 :: Integer)
      d_'43''45'0'45'isCommutativeMonoid_4514
-- Data.Integer.Properties.+-0-abelianGroup
d_'43''45'0'45'abelianGroup_4530 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682
d_'43''45'0'45'abelianGroup_4530
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1808
      MAlonzo.Code.Data.Integer.Base.d__'43'__284 (0 :: Integer)
      MAlonzo.Code.Data.Integer.Base.d_'45'__260
      d_'43''45'0'45'isAbelianGroup_4518
-- Data.Integer.Properties.pos-+
d_pos'45''43'_4532 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pos'45''43'_4532 = erased
-- Data.Integer.Properties.neg-distrib-+
d_neg'45'distrib'45''43'_4544 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'45''43'_4544 = erased
-- Data.Integer.Properties.◃-distrib-+
d_'9667''45'distrib'45''43'_4572 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45'distrib'45''43'_4572 = erased
-- Data.Integer.Properties.+-monoʳ-≤
d_'43''45'mono'691''45''8804'_4590 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'mono'691''45''8804'_4590 v0 v1 v2 v3
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v3 of
            MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
              -> coe
                   d_'8854''45'mono'691''45''8805''45''8804'_3830 (coe v0)
                   (coe subInt (coe (0 :: Integer)) (coe v1))
                   (coe subInt (coe (0 :: Integer)) (coe v2))
                   (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
            MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
              -> coe
                   du_'8804''45'trans_2838
                   (coe
                      d_m'8854'n'8804'm_3722 (coe v0)
                      (coe subInt (coe (0 :: Integer)) (coe v1)))
                   (coe
                      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0)))
            MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
              -> coe
                   MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
                      v0 v1 v2 v6)
            _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v3 of
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
               -> let v7 = subInt (coe (-1 :: Integer)) (coe v1) in
                  coe
                    (let v8 = subInt (coe (-1 :: Integer)) (coe v2) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
                             (subInt (coe (0 :: Integer)) (coe v0)) v8 v7 v6)))
             MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
               -> coe
                    du_'8804''45'trans_2838
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                          (coe subInt (coe (0 :: Integer)) (coe v0))))
                    (coe
                       d_'45'1'43'm'8804'n'8854'm_3802
                       (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v2))
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
               -> coe
                    d_'8854''45'mono'737''45''8804'_3858
                    (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1) (coe v2)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.+-monoˡ-≤
d_'43''45'mono'737''45''8804'_4616 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'mono'737''45''8804'_4616 v0 v1 v2
  = coe d_'43''45'mono'691''45''8804'_4590 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Properties.+-mono-≤
d_'43''45'mono'45''8804'_4632 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'mono'45''8804'_4632 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2908)
         (\ v6 v7 v8 -> coe du_'60''8658''8804'_2954 v8))
      (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v0) (coe v2))
      (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_2908)
            (\ v6 v7 v8 v9 v10 -> coe du_'8804''45''60''45'trans_3066 v9 v10))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v0) (coe v2))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v2))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_2908)
               (\ v6 v7 v8 v9 v10 -> coe du_'8804''45''60''45'trans_3066 v9 v10))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v2))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2908))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3)))
            (d_'43''45'mono'691''45''8804'_4590
               (coe v1) (coe v2) (coe v3) (coe v5)))
         (coe d_'43''45'mono'737''45''8804'_4616 v2 v0 v1 v4))
-- Data.Integer.Properties.i≤j⇒i≤k+j
d_i'8804'j'8658'i'8804'k'43'j_4654 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'i'8804'k'43'j_4654 v0 v1 v2 ~v3 v4
  = du_i'8804'j'8658'i'8804'k'43'j_4654 v0 v1 v2 v4
du_i'8804'j'8658'i'8804'k'43'j_4654 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'j'8658'i'8804'k'43'j_4654 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''8804'_4632 (coe (0 :: Integer)) (coe v2)
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe v3)
-- Data.Integer.Properties.i≤j+i
d_i'8804'j'43'i_4668 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'43'i_4668 v0 v1 ~v2 = du_i'8804'j'43'i_4668 v0 v1
du_i'8804'j'43'i_4668 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'j'43'i_4668 v0 v1
  = coe
      du_i'8804'j'8658'i'8804'k'43'j_4654 (coe v0) (coe v0) (coe v1)
      (coe d_'8804''45'refl_2836 (coe v0))
-- Data.Integer.Properties.i≤i+j
d_i'8804'i'43'j_4680 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'i'43'j_4680 v0 v1 ~v2 = du_i'8804'i'43'j_4680 v0 v1
du_i'8804'i'43'j_4680 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'i'43'j_4680 v0 v1
  = coe du_i'8804'j'43'i_4668 (coe v0) (coe v1)
-- Data.Integer.Properties.+-monoʳ-<
d_'43''45'mono'691''45''60'_4690 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'691''45''60'_4690 v0 v1 v2 v3
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v3 of
            MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v6
              -> coe
                   d_'8854''45'mono'691''45''62''45''60'_3884 (coe v0)
                   (coe subInt (coe (0 :: Integer)) (coe v1))
                   (coe subInt (coe (0 :: Integer)) (coe v2))
                   (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
            MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
              -> coe
                   du_'60''45''8804''45'trans_3080
                   (coe
                      du_m'8854'1'43'n'60'm_3752 (coe v0)
                      (coe subInt (coe (0 :: Integer)) (coe v1)))
                   (coe
                      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0)))
            MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v6
              -> coe
                   MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
                      (coe v0) (coe v6))
            _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v4 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v3 of
                MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v7
                  -> coe
                       MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
                          (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v7))
                MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64
                  -> coe
                       du_'60''45''8804''45'trans_3080
                       (coe
                          MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                             (coe subInt (coe (0 :: Integer)) (coe v0))))
                       (coe
                          d_'45''91'1'43'm'93''8804'n'8854'm'43'1_3786 (coe v4) (coe v2))
                MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v7
                  -> coe
                       d_'8854''45'mono'737''45''60'_3908
                       (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1) (coe v2)
                       (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Integer.Properties.+-monoˡ-<
d_'43''45'mono'737''45''60'_4714 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'737''45''60'_4714 v0 v1 v2
  = coe d_'43''45'mono'691''45''60'_4690 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Properties.+-mono-<
d_'43''45'mono'45''60'_4730 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'45''60'_4730 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
      (coe MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v0) (coe v2))
      (coe MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
            (\ v6 v7 v8 v9 v10 -> coe du_'60''45'trans_3094 v9 v10)
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
            (\ v6 v7 v8 v9 v10 -> coe du_'60''45''8804''45'trans_3080 v9 v10))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v0) (coe v2))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v2))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (\ v6 v7 v8 v9 v10 -> coe du_'60''45'trans_3094 v9 v10)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (\ v6 v7 v8 v9 v10 -> coe du_'60''45''8804''45'trans_3080 v9 v10))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v2))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2908))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v3)))
            (d_'43''45'mono'691''45''60'_4690
               (coe v1) (coe v2) (coe v3) (coe v5)))
         (coe d_'43''45'mono'737''45''60'_4714 v2 v0 v1 v4))
-- Data.Integer.Properties.+-mono-≤-<
d_'43''45'mono'45''8804''45''60'_4748 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'45''8804''45''60'_4748 v0 v1 v2 v3 v4 v5
  = coe
      du_'8804''45''60''45'trans_3066
      (coe d_'43''45'mono'737''45''8804'_4616 v2 v0 v1 v4)
      (coe
         d_'43''45'mono'691''45''60'_4690 (coe v1) (coe v2) (coe v3)
         (coe v5))
-- Data.Integer.Properties.+-mono-<-≤
d_'43''45'mono'45''60''45''8804'_4760 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'43''45'mono'45''60''45''8804'_4760 v0 v1 v2 v3 v4 v5
  = coe
      du_'60''45''8804''45'trans_3080
      (coe d_'43''45'mono'737''45''60'_4714 v2 v0 v1 v4)
      (coe
         d_'43''45'mono'691''45''8804'_4590 (coe v1) (coe v2) (coe v3)
         (coe v5))
-- Data.Integer.Properties.neg-minus-pos
d_neg'45'minus'45'pos_4776 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'minus'45'pos_4776 = erased
-- Data.Integer.Properties.+-minus-telescope
d_'43''45'minus'45'telescope_4792 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'minus'45'telescope_4792 = erased
-- Data.Integer.Properties.[+m]-[+n]≡m⊖n
d_'91''43'm'93''45''91''43'n'93''8801'm'8854'n_4814 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91''43'm'93''45''91''43'n'93''8801'm'8854'n_4814 = erased
-- Data.Integer.Properties.∣i-j∣≡∣j-i∣
d_'8739'i'45'j'8739''8801''8739'j'45'i'8739'_4828 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'i'45'j'8739''8801''8739'j'45'i'8739'_4828 = erased
-- Data.Integer.Properties.∣-∣-≤
d_'8739''45''8739''45''8804'_4858 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''45''8804'_4858 = erased
-- Data.Integer.Properties.i≡j⇒i-j≡0
d_i'8801'j'8658'i'45'j'8801'0_4896 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8801'j'8658'i'45'j'8801'0_4896 = erased
-- Data.Integer.Properties.i-j≡0⇒i≡j
d_i'45'j'8801'0'8658'i'8801'j_4904 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'45'j'8801'0'8658'i'8801'j_4904 = erased
-- Data.Integer.Properties.i≤j⇒i-k≤j
d_i'8804'j'8658'i'45'k'8804'j_4922 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'i'45'k'8804'j_4922 v0 ~v1 v2 ~v3 v4
  = du_i'8804'j'8658'i'45'k'8804'j_4922 v0 v2 v4
du_i'8804'j'8658'i'45'k'8804'j_4922 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'j'8658'i'45'k'8804'j_4922 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
                    coe
                      du_'8804''45'trans_2838
                      (coe d_m'8854'n'8804'm_3722 (coe v0) (coe v1)) (coe v2)
                _ -> let v4 = subInt (coe (-1 :: Integer)) (coe v0) in
                     coe
                       (coe
                          du_'8804''45'trans_2838
                          (coe
                             MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v4))
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                   (coe addInt (coe v4) (coe v3)))))
                          (coe v2)))
-- Data.Integer.Properties.i-j≤i
d_i'45'j'8804'i_4950 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'45'j'8804'i_4950 v0 v1 ~v2 = du_i'45'j'8804'i_4950 v0 v1
du_i'45'j'8804'i_4950 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'45'j'8804'i_4950 v0 v1
  = coe
      du_i'8804'j'8658'i'45'k'8804'j_4922 (coe v0) (coe v1)
      (coe d_'8804''45'refl_2836 (coe v0))
-- Data.Integer.Properties.i≤j⇒i-j≤0
d_i'8804'j'8658'i'45'j'8804'0_4956 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'i'45'j'8804'0_4956 v0 v1 v2
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
                      (coe d_'8804''45'isPreorder_2908)
                      (\ v8 v9 v10 -> coe du_'60''8658''8804'_2954 v10))
                   (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1))
                   MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                      (\ v8 v9 v10 v11 v12 -> v12)
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                         (coe subInt (coe (0 :: Integer)) (coe v1))
                         (coe subInt (coe (0 :: Integer)) (coe v0)))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v7) (coe v6))
                      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe d_'8804''45'isPreorder_2908)
                            (\ v8 v9 v10 v11 v12 ->
                               coe du_'8804''45''60''45'trans_3066 v11 v12))
                         (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v7) (coe v6))
                         (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v7) (coe v7))
                         MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                            (\ v8 v9 v10 v11 v12 -> v12)
                            (MAlonzo.Code.Data.Integer.Base.d__'8854'__266 (coe v7) (coe v7))
                            MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                            MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                  (coe d_'8804''45'isPreorder_2908))
                               (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
                            erased)
                         (d_'8854''45'mono'691''45''8805''45''8804'_3830
                            (coe v7) (coe v6) (coe v7) (coe v5)))
                      erased)))
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe
             du_i'8804'j'8658'i'45'k'8804'j_4922 (coe v0) (coe v1)
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
                                    (coe d_'8804''45'isPreorder_2908)
                                    (\ v11 v12 v13 -> coe du_'60''8658''8804'_2954 v13))
                                 (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1))
                                 MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                    (\ v11 v12 v13 v14 v15 -> v15)
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe v0) (coe v1))
                                    (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                       (coe v10) (coe v6))
                                    MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                          (coe d_'8804''45'isPreorder_2908)
                                          (\ v11 v12 v13 v14 v15 ->
                                             coe du_'8804''45''60''45'trans_3066 v14 v15))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v10) (coe v6))
                                       (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                          (coe v10) (coe v10))
                                       MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                          (\ v11 v12 v13 v14 v15 -> v15)
                                          (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                                             (coe v10) (coe v10))
                                          MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                          MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe d_'8804''45'isPreorder_2908))
                                             (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
                                          erased)
                                       (d_'8854''45'mono'691''45''8805''45''8804'_3830
                                          (coe v10) (coe v6) (coe v10) (coe v9)))
                                    erased))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.i-j≤0⇒i≤j
d_i'45'j'8804'0'8658'i'8804'j_4982 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'45'j'8804'0'8658'i'8804'j_4982 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2908)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_2954 v5))
      v0 v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
         (\ v3 v4 v5 v6 v7 -> v7) v0
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284
            (coe v0) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
            (\ v3 v4 v5 v6 v7 -> v7)
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284
               (coe v0) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284
               (coe v0)
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'43'__284
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))
                  (coe v1)))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
               (\ v3 v4 v5 v6 v7 -> v7)
               (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                  (coe v0)
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'43'__284
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))
                     (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                  (coe MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1))
                  (coe v1))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                     (coe d_'8804''45'isPreorder_2908)
                     (\ v3 v4 v5 v6 v7 -> coe du_'8804''45''60''45'trans_3066 v6 v7))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                     (coe MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1))
                     (coe v1))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                     (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
                  v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                     (\ v3 v4 v5 v6 v7 -> v7)
                     (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                        (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
                     v1 v1
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_2908))
                        (coe v1))
                     erased)
                  (coe
                     d_'43''45'mono'737''45''8804'_4616 v1
                     (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1))
                     MAlonzo.Code.Data.Integer.Base.d_0ℤ_12 v2))
               erased)
            erased)
         erased)
-- Data.Integer.Properties.i≤j⇒0≤j-i
d_i'8804'j'8658'0'8804'j'45'i_4994 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'0'8804'j'45'i_4994 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2908)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_2954 v5))
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1) (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
         (\ v3 v4 v5 v6 v7 -> v7) MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
         (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v0))
         (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1) (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_2908)
               (\ v3 v4 v5 v6 v7 -> coe du_'8804''45''60''45'trans_3066 v6 v7))
            (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v0))
            (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1) (coe v0))
            (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1) (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2908))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v1) (coe v0)))
            (coe
               d_'43''45'mono'737''45''8804'_4616
               (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0)) v0 v1 v2))
         erased)
-- Data.Integer.Properties.0≤i-j⇒j≤i
d_0'8804'i'45'j'8658'j'8804'i_5006 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_0'8804'i'45'j'8658'j'8804'i_5006 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2908)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_2954 v5))
      v1 v0
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
         (\ v3 v4 v5 v6 v7 -> v7) v1
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284
            (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
         v0
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_2908)
               (\ v3 v4 v5 v6 v7 -> coe du_'8804''45''60''45'trans_3066 v6 v7))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284
               (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) (coe v1))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284
               (coe MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1))
               (coe v1))
            v0
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
               (\ v3 v4 v5 v6 v7 -> v7)
               (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                  (coe MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1))
                  (coe v1))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                  (coe v0)
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'43'__284
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))
                     (coe v1)))
               v0
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                  (\ v3 v4 v5 v6 v7 -> v7)
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                     (coe v0)
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'43'__284
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))
                        (coe v1)))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                     (coe v0) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
                  v0
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                     (\ v3 v4 v5 v6 v7 -> v7)
                     (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                        (coe v0) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
                     v0 v0
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_2908))
                        (coe v0))
                     erased)
                  erased)
               erased)
            (coe
               d_'43''45'mono'737''45''8804'_4616 v1
               MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
               (MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0) (coe v1))
               v2))
         erased)
-- Data.Integer.Properties.i≤j⇒i≤1+j
d_i'8804'j'8658'i'8804'1'43'j_5018 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'i'8804'1'43'j_5018 v0 v1
  = coe
      du_i'8804'j'8658'i'8804'k'43'j_4654 (coe v0) (coe v1)
      (coe (1 :: Integer))
-- Data.Integer.Properties.i≤suc[i]
d_i'8804'suc'91'i'93'_5022 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'suc'91'i'93'_5022 v0
  = coe du_i'8804'j'43'i_4668 (coe v0) (coe (1 :: Integer))
-- Data.Integer.Properties.suc-+
d_suc'45''43'_5030 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45''43'_5030 = erased
-- Data.Integer.Properties.i≢suc[i]
d_i'8802'suc'91'i'93'_5040 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_i'8802'suc'91'i'93'_5040 = erased
-- Data.Integer.Properties.1-[1+n]≡-n
d_1'45''91'1'43'n'93''8801''45'n_5046 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'45''91'1'43'n'93''8801''45'n_5046 = erased
-- Data.Integer.Properties.suc-mono
d_suc'45'mono_5050 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_suc'45'mono_5050 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v5
        -> coe
             d_'8854''45'mono'691''45''8805''45''8804'_3830 (coe (1 :: Integer))
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
                   (coe d_'8804''45'isPreorder_2908)
                   (\ v6 v7 v8 -> coe du_'60''8658''8804'_2954 v8))
                (coe
                   MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                   MAlonzo.Code.Data.Integer.Base.d_suc_308 (\ v6 v7 -> v6) v0 v1)
                (coe
                   MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                   (\ v6 v7 -> v7) MAlonzo.Code.Data.Integer.Base.d_suc_308 v0 v1)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                   (\ v6 v7 v8 v9 v10 -> v10)
                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                      (coe (1 :: Integer)) (coe subInt (coe (0 :: Integer)) (coe v0)))
                   (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                      (coe (0 :: Integer)) (coe v5))
                   (coe
                      MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                      (\ v6 v7 -> v7) MAlonzo.Code.Data.Integer.Base.d_suc_308 v0 v1)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe d_'8804''45'isPreorder_2908)
                         (\ v6 v7 v8 v9 v10 -> coe du_'8804''45''60''45'trans_3066 v9 v10))
                      (MAlonzo.Code.Data.Integer.Base.d__'8854'__266
                         (coe (0 :: Integer)) (coe v5))
                      (MAlonzo.Code.Data.Integer.Base.d_suc_308 (coe v1))
                      (coe
                         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                         (\ v6 v7 -> v7) MAlonzo.Code.Data.Integer.Base.d_suc_308 v0 v1)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe d_'8804''45'isPreorder_2908))
                         (coe MAlonzo.Code.Data.Integer.Base.d_suc_308 (coe v1)))
                      (coe du_0'8854'm'8804''43'_3812 (coe v5)))
                   erased))
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v5
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.suc[i]≤j⇒i<j
d_suc'91'i'93''8804'j'8658'i'60'j_5064 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_suc'91'i'93''8804'j'8658'i'60'j_5064 v0 v1 v2
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
d_i'60'j'8658'suc'91'i'93''8804'j_5084 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'60'j'8658'suc'91'i'93''8804'j_5084 v0 v1 v2
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
d_suc'45'pred_5096 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'pred_5096 = erased
-- Data.Integer.Properties.pred-suc
d_pred'45'suc_5106 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'45'suc_5106 = erased
-- Data.Integer.Properties.+-pred
d_'43''45'pred_5118 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'pred_5118 = erased
-- Data.Integer.Properties.pred-+
d_pred'45''43'_5134 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'45''43'_5134 = erased
-- Data.Integer.Properties.neg-suc
d_neg'45'suc_5146 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'suc_5146 = erased
-- Data.Integer.Properties.minus-suc
d_minus'45'suc_5154 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_minus'45'suc_5154 = erased
-- Data.Integer.Properties.i≤pred[j]⇒i<j
d_i'8804'pred'91'j'93''8658'i'60'j_5164 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_i'8804'pred'91'j'93''8658'i'60'j_5164 ~v0 v1 v2
  = du_i'8804'pred'91'j'93''8658'i'60'j_5164 v1 v2
du_i'8804'pred'91'j'93''8658'i'60'j_5164 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_i'8804'pred'91'j'93''8658'i'60'j_5164 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            du_'8804''45''60''45'trans_3066 (coe v1)
            (coe du_m'8854'1'43'n'60'm_3752 (coe v0) (coe (1 :: Integer)))
      _ -> coe
             du_'8804''45''60''45'trans_3066 (coe v1)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                   (coe subInt (coe (0 :: Integer)) (coe v0))))
-- Data.Integer.Properties.i<j⇒i≤pred[j]
d_i'60'j'8658'i'8804'pred'91'j'93'_5174 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'60'j'8658'i'8804'pred'91'j'93'_5174 ~v0 v1 v2
  = du_i'60'j'8658'i'8804'pred'91'j'93'_5174 v1 v2
du_i'60'j'8658'i'8804'pred'91'j'93'_5174 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'60'j'8658'i'8804'pred'91'j'93'_5174 v0 v1
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
d_i'8804'j'8658'pred'91'i'93''8804'j_5186 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_i'8804'j'8658'pred'91'i'93''8804'j_5186 ~v0 ~v1 v2
  = du_i'8804'j'8658'pred'91'i'93''8804'j_5186 v2
du_i'8804'j'8658'pred'91'i'93''8804'j_5186 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_i'8804'j'8658'pred'91'i'93''8804'j_5186 v0
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
d_pred'45'mono_5192 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_pred'45'mono_5192 v0 v1 v2
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
             d_'8854''45'mono'737''45''8804'_3858 (coe (1 :: Integer)) (coe v0)
             (coe v1) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.*-comm
d_'42''45'comm_5200 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_5200 = erased
-- Data.Integer.Properties.*-identityˡ
d_'42''45'identity'737'_5234 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_5234 = erased
-- Data.Integer.Properties.*-identityʳ
d_'42''45'identity'691'_5248 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_5248 = erased
-- Data.Integer.Properties.*-identity
d_'42''45'identity_5250 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_5250
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.*-zeroˡ
d_'42''45'zero'737'_5252 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'737'_5252 = erased
-- Data.Integer.Properties.*-zeroʳ
d_'42''45'zero'691'_5254 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'691'_5254 = erased
-- Data.Integer.Properties.*-zero
d_'42''45'zero_5256 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'zero_5256
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.*-assoc
d_'42''45'assoc_5258 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_5258 = erased
-- Data.Integer.Properties.distrib-lemma
d_distrib'45'lemma_5336 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'45'lemma_5336 = erased
-- Data.Integer.Properties.*-distribʳ-+
d_'42''45'distrib'691''45''43'_5412 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''43'_5412 = erased
-- Data.Integer.Properties.*-distribˡ-+
d_'42''45'distrib'737''45''43'_5674 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''43'_5674 = erased
-- Data.Integer.Properties.*-distrib-+
d_'42''45'distrib'45''43'_5676 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''43'_5676
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.*-isMagma
d_'42''45'isMagma_5678 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_5678
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Integer.Properties.*-isSemigroup
d_'42''45'isSemigroup_5680 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_5680
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe d_'42''45'isMagma_5678) erased
-- Data.Integer.Properties.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_5682 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_5682
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_608
      (coe d_'42''45'isSemigroup_5680) erased
-- Data.Integer.Properties.*-1-isMonoid
d_'42''45'1'45'isMonoid_5684 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'1'45'isMonoid_5684
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe d_'42''45'isSemigroup_5680) (coe d_'42''45'identity_5250)
-- Data.Integer.Properties.*-1-isCommutativeMonoid
d_'42''45'1'45'isCommutativeMonoid_5686 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'1'45'isCommutativeMonoid_5686
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe d_'42''45'1'45'isMonoid_5684) erased
-- Data.Integer.Properties.+-*-isSemiring
d_'43''45''42''45'isSemiring_5688 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_'43''45''42''45'isSemiring_5688
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1740
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1630
         (coe d_'43''45'0'45'isCommutativeMonoid_4514) erased erased
         (coe d_'42''45'identity_5250) (coe d_'42''45'distrib'45''43'_5676))
      (coe d_'42''45'zero_5256)
-- Data.Integer.Properties.+-*-isCommutativeSemiring
d_'43''45''42''45'isCommutativeSemiring_5690 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_'43''45''42''45'isCommutativeSemiring_5690
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe d_'43''45''42''45'isSemiring_5688) erased
-- Data.Integer.Properties.+-*-isRing
d_'43''45''42''45'isRing_5692 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_'43''45''42''45'isRing_5692
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_2876
      (coe d_'43''45'0'45'isAbelianGroup_4518) erased erased
      (coe d_'42''45'identity_5250) (coe d_'42''45'distrib'45''43'_5676)
-- Data.Integer.Properties.+-*-isCommutativeRing
d_'43''45''42''45'isCommutativeRing_5694 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888
d_'43''45''42''45'isCommutativeRing_5694
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_3030
      (coe d_'43''45''42''45'isRing_5692) erased
-- Data.Integer.Properties.*-magma
d_'42''45'magma_5696 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'42''45'magma_5696
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124
      MAlonzo.Code.Data.Integer.Base.d__'42'__316 d_'42''45'isMagma_5678
-- Data.Integer.Properties.*-semigroup
d_'42''45'semigroup_5698 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'42''45'semigroup_5698
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      d_'42''45'isSemigroup_5680
-- Data.Integer.Properties.*-commutativeSemigroup
d_'42''45'commutativeSemigroup_5700 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'42''45'commutativeSemigroup_5700
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_754
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      d_'42''45'isCommutativeSemigroup_5682
-- Data.Integer.Properties.*-1-monoid
d_'42''45'1'45'monoid_5702 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'42''45'1'45'monoid_5702
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16 d_'42''45'1'45'isMonoid_5684
-- Data.Integer.Properties.*-1-commutativeMonoid
d_'42''45'1'45'commutativeMonoid_5704 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'42''45'1'45'commutativeMonoid_5704
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'42''45'1'45'isCommutativeMonoid_5686
-- Data.Integer.Properties.+-*-semiring
d_'43''45''42''45'semiring_5706 ::
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2356
d_'43''45''42''45'semiring_5706
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2518
      MAlonzo.Code.Data.Integer.Base.d__'43'__284
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'43''45''42''45'isSemiring_5688
-- Data.Integer.Properties.+-*-commutativeSemiring
d_'43''45''42''45'commutativeSemiring_5708 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
d_'43''45''42''45'commutativeSemiring_5708
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2706
      MAlonzo.Code.Data.Integer.Base.d__'43'__284
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'43''45''42''45'isCommutativeSemiring_5690
-- Data.Integer.Properties.+-*-ring
d_'43''45''42''45'ring_5710 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3908
d_'43''45''42''45'ring_5710
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_4120
      MAlonzo.Code.Data.Integer.Base.d__'43'__284
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      MAlonzo.Code.Data.Integer.Base.d_'45'__260
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'43''45''42''45'isRing_5692
-- Data.Integer.Properties.+-*-commutativeRing
d_'43''45''42''45'commutativeRing_5712 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4126
d_'43''45''42''45'commutativeRing_5712
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_4352
      MAlonzo.Code.Data.Integer.Base.d__'43'__284
      MAlonzo.Code.Data.Integer.Base.d__'42'__316
      MAlonzo.Code.Data.Integer.Base.d_'45'__260
      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
      MAlonzo.Code.Data.Integer.Base.d_1ℤ_16
      d_'43''45''42''45'isCommutativeRing_5694
-- Data.Integer.Properties.abs-*
d_abs'45''42'_5714 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45''42'_5714 = erased
-- Data.Integer.Properties.sign-*
d_sign'45''42'_5724 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'45''42'_5724 = erased
-- Data.Integer.Properties.*-cancelʳ-≡
d_'42''45'cancel'691''45''8801'_5742 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'691''45''8801'_5742 = erased
-- Data.Integer.Properties.*-cancelˡ-≡
d_'42''45'cancel'737''45''8801'_5786 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45''8801'_5786 = erased
-- Data.Integer.Properties.suc-*
d_suc'45''42'_5806 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45''42'_5806 = erased
-- Data.Integer.Properties.*-suc
d_'42''45'suc_5822 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'suc_5822 = erased
-- Data.Integer.Properties.-1*i≡-i
d_'45'1'42'i'8801''45'i_5836 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45'1'42'i'8801''45'i_5836 = erased
-- Data.Integer.Properties.i*j≡0⇒i≡0∨j≡0
d_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5846 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5846 v0 ~v1 ~v2
  = du_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5846 v0
du_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5846 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5846 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3940
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
-- Data.Integer.Properties.i*j≢0
d_i'42'j'8802'0_5876 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_i'42'j'8802'0_5876 ~v0 ~v1 ~v2 ~v3 = du_i'42'j'8802'0_5876
du_i'42'j'8802'0_5876 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_i'42'j'8802'0_5876
  = coe MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0_3958
-- Data.Integer.Properties.^-identityʳ
d_'94''45'identity'691'_5888 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'identity'691'_5888 = erased
-- Data.Integer.Properties.^-zeroˡ
d_'94''45'zero'737'_5892 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'zero'737'_5892 = erased
-- Data.Integer.Properties.^-distribˡ-+-*
d_'94''45'distrib'737''45''43''45''42'_5906 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'distrib'737''45''43''45''42'_5906 = erased
-- Data.Integer.Properties.^-isMagmaHomomorphism
d_'94''45'isMagmaHomomorphism_5928 ::
  Integer ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_194
d_'94''45'isMagmaHomomorphism_5928 ~v0
  = du_'94''45'isMagmaHomomorphism_5928
du_'94''45'isMagmaHomomorphism_5928 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_194
du_'94''45'isMagmaHomomorphism_5928
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.Structures.C_constructor_54
         erased)
      erased
-- Data.Integer.Properties.^-isMonoidHomomorphism
d_'94''45'isMonoidHomomorphism_5938 ::
  Integer ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_380
d_'94''45'isMonoidHomomorphism_5938 ~v0
  = du_'94''45'isMonoidHomomorphism_5938
du_'94''45'isMonoidHomomorphism_5938 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_380
du_'94''45'isMonoidHomomorphism_5938
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_constructor_400
      (coe du_'94''45'isMagmaHomomorphism_5928) erased
-- Data.Integer.Properties.^-*-assoc
d_'94''45''42''45'assoc_5948 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45''42''45'assoc_5948 = erased
-- Data.Integer.Properties.i^n≡0⇒i≡0
d_i'94'n'8801'0'8658'i'8801'0_5974 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'94'n'8801'0'8658'i'8801'0_5974 = erased
-- Data.Integer.Properties.pos-*
d_pos'45''42'_5982 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pos'45''42'_5982 = erased
-- Data.Integer.Properties.neg-distribˡ-*
d_neg'45'distrib'737''45''42'_5996 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'737''45''42'_5996 = erased
-- Data.Integer.Properties.neg-distribʳ-*
d_neg'45'distrib'691''45''42'_6012 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'691''45''42'_6012 = erased
-- Data.Integer.Properties.◃-distrib-*
d_'9667''45'distrib'45''42'_6030 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45'distrib'45''42'_6030 = erased
-- Data.Integer.Properties.*-cancelʳ-≤-pos
d_'42''45'cancel'691''45''8804''45'pos_6064 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'cancel'691''45''8804''45'pos_6064 v0 v1 ~v2 ~v3 v4
  = du_'42''45'cancel'691''45''8804''45'pos_6064 v0 v1 v4
du_'42''45'cancel'691''45''8804''45'pos_6064 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'cancel'691''45''8804''45'pos_6064 v0 v1 v2
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
                  MAlonzo.Code.Data.Nat.Properties.du_'42''45'cancel'691''45''8804'_4184
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
                             MAlonzo.Code.Data.Nat.Properties.du_'42''45'cancel'691''45''8804'_4184
                             (coe subInt (coe (0 :: Integer)) (coe v1)))))
-- Data.Integer.Properties.*-cancelˡ-≤-pos
d_'42''45'cancel'737''45''8804''45'pos_6098 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'cancel'737''45''8804''45'pos_6098 v0 v1 ~v2 ~v3
  = du_'42''45'cancel'737''45''8804''45'pos_6098 v0 v1
du_'42''45'cancel'737''45''8804''45'pos_6098 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'cancel'737''45''8804''45'pos_6098 v0 v1
  = coe
      du_'42''45'cancel'691''45''8804''45'pos_6064 (coe v0) (coe v1)
-- Data.Integer.Properties.*-monoʳ-≤-nonNeg
d_'42''45'mono'691''45''8804''45'nonNeg_6120 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'nonNeg_6120 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'691''45''8804''45'nonNeg_6120 v0 v2 v3 v4
du_'42''45'mono'691''45''8804''45'nonNeg_6120 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'mono'691''45''8804''45'nonNeg_6120 v0 v1 v2 v3
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
                          MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'45''8804'_4214
                          (coe subInt (coe (0 :: Integer)) (coe v1)) (coe v0)
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))))
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
                              MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'737''45''8804'_4222
                              v0 v1 v2 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.*-monoˡ-≤-nonNeg
d_'42''45'mono'737''45''8804''45'nonNeg_6162 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'nonNeg_6162 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804''45'nonNeg_6162 v0 v2 v3
du_'42''45'mono'737''45''8804''45'nonNeg_6162 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'mono'737''45''8804''45'nonNeg_6162 v0 v1 v2
  = coe
      du_'42''45'mono'691''45''8804''45'nonNeg_6120 (coe v0) (coe v1)
      (coe v2)
-- Data.Integer.Properties.*-cancelˡ-≤-neg
d_'42''45'cancel'737''45''8804''45'neg_6186 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_170 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'cancel'737''45''8804''45'neg_6186 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''8804''45'neg_6186 v0 v1 v2 v4
du_'42''45'cancel'737''45''8804''45'neg_6186 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'cancel'737''45''8804''45'neg_6186 v0 v1 v2 v3
  = coe
      d_neg'45'cancel'45''8804'_3386 (coe v1) (coe v2)
      (coe
         du_'42''45'cancel'737''45''8804''45'pos_6098
         (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))
         (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe d_'8804''45'isPreorder_2908)
               (\ v4 v5 v6 -> coe du_'60''8658''8804'_2954 v6))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
               (\ v4 v5 v6 v7 v8 -> v8)
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__316
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                     (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                  (\ v4 v5 v6 v7 v8 -> v8)
                  (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__316
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                        (coe v1)))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                        (coe d_'8804''45'isPreorder_2908)
                        (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_3066 v7 v8))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v2))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                        (\ v4 v5 v6 v7 v8 -> v8)
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v2))
                        (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                           (coe
                              MAlonzo.Code.Data.Integer.Base.d__'42'__316
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                              (coe v2)))
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                           (\ v4 v5 v6 v7 v8 -> v8)
                           (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                              (coe
                                 MAlonzo.Code.Data.Integer.Base.d__'42'__316
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                                 (coe v2)))
                           (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
                           (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                 (coe d_'8804''45'isPreorder_2908))
                              (coe
                                 MAlonzo.Code.Data.Integer.Base.d__'42'__316
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))))
                           erased)
                        erased)
                     v3)
                  erased)
               erased)))
-- Data.Integer.Properties.*-cancelʳ-≤-neg
d_'42''45'cancel'691''45''8804''45'neg_6208 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_170 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'cancel'691''45''8804''45'neg_6208 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''8804''45'neg_6208 v0 v1 v2
du_'42''45'cancel'691''45''8804''45'neg_6208 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'cancel'691''45''8804''45'neg_6208 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''8804''45'neg_6186 (coe v2) (coe v0)
      (coe v1)
-- Data.Integer.Properties.*-monoˡ-≤-nonPos
d_'42''45'mono'737''45''8804''45'nonPos_6230 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'nonPos_6230 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''8804''45'nonPos_6230 v0 v2 v3 v4
du_'42''45'mono'737''45''8804''45'nonPos_6230 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'mono'737''45''8804''45'nonPos_6230 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                (coe d_'8804''45'isPreorder_2908)
                (\ v4 v5 v6 -> coe du_'60''8658''8804'_2954 v6))
             (coe
                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                (\ v4 v5 -> v5)
                (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0)) v1 v2)
             (coe
                MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0))
                (\ v4 v5 -> v4) v1 v2)
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                (\ v4 v5 v6 v7 v8 -> v8)
                (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v2))
                (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d__'42'__316
                      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                      (coe v2)))
                (coe
                   MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0))
                   (\ v4 v5 -> v4) v1 v2)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                   (\ v4 v5 v6 v7 v8 -> v8)
                   (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d__'42'__316
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                         (coe v2)))
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
                   (coe
                      MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0))
                      (\ v4 v5 -> v4) v1 v2)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe d_'8804''45'isPreorder_2908)
                         (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_3066 v7 v8))
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                      (coe
                         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0))
                         (\ v4 v5 -> v4) v1 v2)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                         (\ v4 v5 v6 v7 v8 -> v8)
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                            (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                            (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                         (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__316
                               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                               (coe v1)))
                         (coe
                            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                            (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0))
                            (\ v4 v5 -> v4) v1 v2)
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                            (\ v4 v5 v6 v7 v8 -> v8)
                            (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__316
                                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                                  (coe v1)))
                            (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
                            (coe
                               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                               (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0))
                               (\ v4 v5 -> v4) v1 v2)
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                  (coe d_'8804''45'isPreorder_2908))
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1)))
                            erased)
                         erased)
                      (coe
                         du_'42''45'mono'737''45''8804''45'nonNeg_6162
                         (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                         (coe
                            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                            (\ v4 v5 -> v5) MAlonzo.Code.Data.Integer.Base.d_'45'__260 v1 v2)
                         (coe
                            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                            MAlonzo.Code.Data.Integer.Base.d_'45'__260 (\ v4 v5 -> v4) v1 v2)
                         (coe du_neg'45'mono'45''8804'_3380 (coe v2) (coe v3))))
                   erased)
                erased)
-- Data.Integer.Properties.*-monoʳ-≤-nonPos
d_'42''45'mono'691''45''8804''45'nonPos_6258 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'nonPos_6258 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804''45'nonPos_6258 v0 v2 v3
du_'42''45'mono'691''45''8804''45'nonPos_6258 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'42''45'mono'691''45''8804''45'nonPos_6258 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''8804''45'nonPos_6230 (coe v0) (coe v1)
      (coe v2)
-- Data.Integer.Properties.*-monoˡ-<-pos
d_'42''45'mono'737''45''60''45'pos_6280 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'mono'737''45''60''45'pos_6280 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60''45'pos_6280 v0 v2 v3 v4
du_'42''45'mono'737''45''60''45'pos_6280 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'mono'737''45''60''45'pos_6280 v0 v1 v2 v3
  = let v4 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v1 of
         _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
             case coe v3 of
               MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72 v7
                 -> coe
                      du_'43''9667''45'mono'45''60'_4172
                      (coe addInt (coe v1) (coe mulInt (coe v4) (coe v1)))
                      (coe
                         MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''60''45''8804'_3686
                         (coe v7)
                         (coe
                            MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                            v4 v1 v2
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                               (coe v7))))
               _ -> MAlonzo.RTE.mazUnreachableError
         _ -> case coe v2 of
                _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
                    coe du_'45''9667''60''43''9667'_4214 (coe mulInt (coe v0) (coe v2))
                _ -> case coe v3 of
                       MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58 v7
                         -> coe
                              MAlonzo.Code.Data.Integer.Base.C_'45''60''45'_58
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''60''45''8804'_3686
                                 (coe v7)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                                    v4 (subInt (coe (0 :: Integer)) (coe v2))
                                    (subInt (coe (0 :: Integer)) (coe v1))
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Integer.Properties.*-monoʳ-<-pos
d_'42''45'mono'691''45''60''45'pos_6312 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'mono'691''45''60''45'pos_6312 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''60''45'pos_6312 v0 v2 v3
du_'42''45'mono'691''45''60''45'pos_6312 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'mono'691''45''60''45'pos_6312 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''60''45'pos_6280 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Properties.*-cancelˡ-<-nonNeg
d_'42''45'cancel'737''45''60''45'nonNeg_6332 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'737''45''60''45'nonNeg_6332 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''60''45'nonNeg_6332 v0 v1 v2 v4
du_'42''45'cancel'737''45''60''45'nonNeg_6332 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'cancel'737''45''60''45'nonNeg_6332 v0 v1 v2 v3
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d_'42''45'cancel'737''45''60'_4354
                     v2 (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                     (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
                     (coe
                        du_'43''9667''45'cancel'45''60'_4184
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
                          MAlonzo.Code.Data.Nat.Properties.d_'42''45'cancel'737''45''60'_4354
                          v2 (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
                          (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                          (coe
                             du_neg'9667''45'cancel'45''60'_4198
                             (coe
                                mulInt (coe v2)
                                (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                             (coe v3))))
-- Data.Integer.Properties.*-cancelʳ-<-nonNeg
d_'42''45'cancel'691''45''60''45'nonNeg_6370 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'691''45''60''45'nonNeg_6370 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''60''45'nonNeg_6370 v0 v1 v2
du_'42''45'cancel'691''45''60''45'nonNeg_6370 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'cancel'691''45''60''45'nonNeg_6370 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonNeg_6332 (coe v0) (coe v1)
      (coe v2)
-- Data.Integer.Properties.*-monoˡ-<-neg
d_'42''45'mono'737''45''60''45'neg_6392 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_170 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'mono'737''45''60''45'neg_6392 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60''45'neg_6392 v0 v2 v3 v4
du_'42''45'mono'737''45''60''45'neg_6392 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'mono'737''45''60''45'neg_6392 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
      (coe MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v2))
      (coe MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
         (\ v4 v5 v6 v7 v8 -> v8)
         (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v2))
         (MAlonzo.Code.Data.Integer.Base.d_'45'__260
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
               (coe v2)))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
            (\ v4 v5 v6 v7 v8 -> v8)
            (MAlonzo.Code.Data.Integer.Base.d_'45'__260
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                  (coe v2)))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (\ v4 v5 v6 v7 v8 -> coe du_'60''45'trans_3094 v7 v8)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (\ v4 v5 v6 v7 v8 -> coe du_'60''45''8804''45'trans_3080 v7 v8))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                  (\ v4 v5 v6 v7 v8 -> v8)
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                  (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__316
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                        (coe v1)))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                     (\ v4 v5 v6 v7 v8 -> v8)
                     (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__316
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                           (coe v1)))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_2908))
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v0) (coe v1)))
                     erased)
                  erased)
               (coe
                  du_'42''45'mono'737''45''60''45'pos_6280
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5) MAlonzo.Code.Data.Integer.Base.d_'45'__260 v1 v2)
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     MAlonzo.Code.Data.Integer.Base.d_'45'__260 (\ v4 v5 -> v4) v1 v2)
                  (coe d_neg'45'mono'45''60'_3410 (coe v1) (coe v2) (coe v3))))
            erased)
         erased)
-- Data.Integer.Properties.*-monoʳ-<-neg
d_'42''45'mono'691''45''60''45'neg_6412 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_170 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'mono'691''45''60''45'neg_6412 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''60''45'neg_6412 v0 v2 v3
du_'42''45'mono'691''45''60''45'neg_6412 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'mono'691''45''60''45'neg_6412 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''60''45'neg_6392 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Properties.*-cancelˡ-<-nonPos
d_'42''45'cancel'737''45''60''45'nonPos_6432 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'737''45''60''45'nonPos_6432 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''60''45'nonPos_6432 v0 v1 v2 v4
du_'42''45'cancel'737''45''60''45'nonPos_6432 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'cancel'737''45''60''45'nonPos_6432 v0 v1 v2 v3
  = coe
      d_neg'45'cancel'45''60'_3424 (coe v0) (coe v1)
      (coe
         du_'42''45'cancel'737''45''60''45'nonNeg_6332
         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))
         (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0)))
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
               (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
               (\ v4 v5 v6 v7 v8 -> v8)
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v0)))
               (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__316
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                     (coe v0)))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                  (\ v4 v5 v6 v7 v8 -> v8)
                  (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__316
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                        (coe v0)))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v2) (coe v0))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                        (\ v4 v5 v6 v7 v8 -> coe du_'60''45'trans_3094 v7 v8)
                        (coe
                           MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                        (\ v4 v5 v6 v7 v8 -> coe du_'60''45''8804''45'trans_3080 v7 v8))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v2) (coe v0))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v2) (coe v1))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                        (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                        (\ v4 v5 v6 v7 v8 -> v8)
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v2) (coe v1))
                        (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                           (coe
                              MAlonzo.Code.Data.Integer.Base.d__'42'__316
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                              (coe v1)))
                        (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                           (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                           (\ v4 v5 v6 v7 v8 -> v8)
                           (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                              (coe
                                 MAlonzo.Code.Data.Integer.Base.d__'42'__316
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                                 (coe v1)))
                           (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                           (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                 (coe d_'8804''45'isPreorder_2908))
                              (coe
                                 MAlonzo.Code.Data.Integer.Base.d__'42'__316
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2))
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1))))
                           erased)
                        erased)
                     v3)
                  erased)
               erased)))
-- Data.Integer.Properties.*-cancelʳ-<-nonPos
d_'42''45'cancel'691''45''60''45'nonPos_6454 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'691''45''60''45'nonPos_6454 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''60''45'nonPos_6454 v0 v1 v2
du_'42''45'cancel'691''45''60''45'nonPos_6454 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'42''45'cancel'691''45''60''45'nonPos_6454 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonPos_6432 (coe v0) (coe v1)
      (coe v2)
-- Data.Integer.Properties.*-cancelˡ-<-neg
d_'42''45'cancel'737''45''60''45'neg_6472 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'737''45''60''45'neg_6472 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonPos_6432 (coe v0) (coe v1)
      (coe subInt (coe (-1 :: Integer)) (coe v2))
-- Data.Integer.Properties.*-cancelʳ-<-neg
d_'42''45'cancel'691''45''60''45'neg_6482 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'691''45''60''45'neg_6482 v0 v1 v2
  = coe
      du_'42''45'cancel'691''45''60''45'nonPos_6454 (coe v0) (coe v1)
      (coe subInt (coe (-1 :: Integer)) (coe v2))
-- Data.Integer.Properties.∣i*j∣≡∣i∣*∣j∣
d_'8739'i'42'j'8739''8801''8739'i'8739''42''8739'j'8739'_6494 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'i'42'j'8739''8801''8739'i'8739''42''8739'j'8739'_6494
  = erased
-- Data.Integer.Properties.i≤j⇒i⊓j≡i
d_i'8804'j'8658'i'8851'j'8801'i_6496 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8804'j'8658'i'8851'j'8801'i_6496 = erased
-- Data.Integer.Properties.i≥j⇒i⊓j≡j
d_i'8805'j'8658'i'8851'j'8801'j_6502 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8805'j'8658'i'8851'j'8801'j_6502 = erased
-- Data.Integer.Properties.i≤j⇒i⊔j≡j
d_i'8804'j'8658'i'8852'j'8801'j_6508 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8804'j'8658'i'8852'j'8801'j_6508 = erased
-- Data.Integer.Properties.i≥j⇒i⊔j≡i
d_i'8805'j'8658'i'8852'j'8801'i_6514 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_i'8805'j'8658'i'8852'j'8801'i_6514 = erased
-- Data.Integer.Properties.⊓-operator
d_'8851''45'operator_6520 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106
d_'8851''45'operator_6520
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_constructor_136
      (coe MAlonzo.Code.Data.Integer.Base.d__'8851'__348) erased erased
-- Data.Integer.Properties.⊔-operator
d_'8852''45'operator_6522 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138
d_'8852''45'operator_6522
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_constructor_168
      (coe MAlonzo.Code.Data.Integer.Base.d__'8852'__330) erased erased
-- Data.Integer.Properties.⊓-⊔-properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_6526 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8851'_6526 = erased
-- Data.Integer.Properties.⊓-⊔-properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_6528 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8852'_6528 = erased
-- Data.Integer.Properties.⊓-⊔-properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_6530 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8851'_6530 = erased
-- Data.Integer.Properties.⊓-⊔-properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_6532 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8852'_6532 = erased
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_6534 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'x_6534
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_6536 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8658'x'8851'z'8804'y_6536
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3276
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_6538 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8658'z'8851'x'8804'y_6538
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3288
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_6540 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8658'x'8851'z'8804'y_6540
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3276
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_6542 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8658'z'8851'x'8804'y_6542
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3288
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_6544 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8851'z'8658'x'8804'y_6544
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3300
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_6546 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8851'z'8658'x'8804'z_6546
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3314
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_6548 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'y_6548
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_6550 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8776'x'8658'x'8804'y_6550
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_6552 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8776'y'8658'y'8804'x_6552
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_6554 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'x_6554
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤x⊔y
d_x'8851'y'8804'x'8852'y_6556 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'x'8852'y_6556
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_x'8851'y'8804'x'8852'y_3440
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_6558 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8804'y_6558
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_6560 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8776'x'8658'x'8804'y_6560
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_6562 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8851'y'8776'y'8658'y'8804'x_6562
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_6564 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8851'z'8658'x'8804'y_6564
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3300
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_6566 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_x'8804'y'8851'z'8658'x'8804'z_6566
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3314
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-absorbs-⊔
d_'8851''45'absorbs'45''8852'_6568 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'absorbs'45''8852'_6568 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_6570 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_6570 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_6572 :: MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8851''45'band_6572
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3168
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_6574 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_6574 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_6576 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'8851''45'commutativeSemigroup_6576
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3170
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-cong
d_'8851''45'cong_6578 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong_6578 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-congʳ
d_'8851''45'cong'691'_6580 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong'691'_6580 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-congˡ
d_'8851''45'cong'737'_6582 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong'737'_6582 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-distrib-⊔
d_'8851''45'distrib'45''8852'_6584 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'distrib'45''8852'_6584
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3260
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-properties.⊓-distribʳ-⊔
d_'8851''45'distrib'691''45''8852'_6586 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'691''45''8852'_6586 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-distribˡ-⊔
d_'8851''45'distrib'737''45''8852'_6588 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'737''45''8852'_6588 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_6590 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'glb_6590
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_6592 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_6592 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-identity
d_'8851''45'identity_6594 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_6594 ~v0 ~v1 = du_'8851''45'identity_6594
du_'8851''45'identity_6594 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_6594
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-identityʳ
d_'8851''45'identity'691'_6596 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'identity'691'_6596 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-identityˡ
d_'8851''45'identity'737'_6598 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'identity'737'_6598 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_6600 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8851''45'isBand_6600
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3150
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_6602 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'8851''45'isCommutativeSemigroup_6602
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3152
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_6604 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8851''45'isMagma_6604
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3146
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isMonoid
d_'8851''45'isMonoid_6606 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8851''45'isMonoid_6606
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3158
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_6608 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_'8851''45'isSelectiveMagma_6608
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_6610 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8851''45'isSemigroup_6610
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3148
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_6612 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8851''45'magma_6612
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3164
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_6614 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'45''8804'_6614
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoid
d_'8851''45'monoid_6616 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8851''45'monoid_6616
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3176
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_6618 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'691''45''8804'_6618
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_6620 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'737''45''8804'_6620
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3372
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-rawMagma
d_'8851''45'rawMagma_6622 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8851''45'rawMagma_6622
  = let v0 = d_'8851''45'operator_6520 in
    coe
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'rawMagma_3162
         (coe v0))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_6624 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_6624
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_6626 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
d_'8851''45'selectiveMagma_6626
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3172
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_6628 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8851''45'semigroup_6628
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3166
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_6630 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_6630 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-zero
d_'8851''45'zero_6632 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_6632 ~v0 ~v1 = du_'8851''45'zero_6632
du_'8851''45'zero_6632 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_6632
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-zeroʳ
d_'8851''45'zero'691'_6634 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'691'_6634 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-zeroˡ
d_'8851''45'zero'737'_6636 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'737'_6636 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-⊔-absorptive
d_'8851''45''8852''45'absorptive_6638 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45''8852''45'absorptive_6638
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'absorptive_3340
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-properties.⊔-absorbs-⊓
d_'8852''45'absorbs'45''8851'_6640 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'absorbs'45''8851'_6640 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_6642 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_6642 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_6644 :: MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8851''45'band_6644
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3168
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_6646 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_6646 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_6648 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'8851''45'commutativeSemigroup_6648
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3170
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-cong
d_'8851''45'cong_6650 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong_6650 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-congʳ
d_'8851''45'cong'691'_6652 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong'691'_6652 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-congˡ
d_'8851''45'cong'737'_6654 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong'737'_6654 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊔-distrib-⊓
d_'8852''45'distrib'45''8851'_6656 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'distrib'45''8851'_6656
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'45''8851'_3292
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-properties.⊔-distribʳ-⊓
d_'8852''45'distrib'691''45''8851'_6658 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'691''45''8851'_6658 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊔-distribˡ-⊓
d_'8852''45'distrib'737''45''8851'_6660 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'737''45''8851'_6660 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_6662 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_6662 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-identity
d_'8851''45'identity_6664 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_6664
  = let v0 = d_'8852''45'operator_6522 in
    coe
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
                      v0 v1 v3 (coe v2 v3)))
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
                      v0 v3 v1 (coe v2 v3)))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-identityʳ
d_'8851''45'identity'691'_6666 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'identity'691'_6666 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-identityˡ
d_'8851''45'identity'737'_6668 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'identity'737'_6668 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_6670 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8851''45'isBand_6670
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3150
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_6672 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'8851''45'isCommutativeSemigroup_6672
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3152
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_6674 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8851''45'isMagma_6674
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3146
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isMonoid
d_'8851''45'isMonoid_6676 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8851''45'isMonoid_6676
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3158
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_6678 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_'8851''45'isSelectiveMagma_6678
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_6680 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8851''45'isSemigroup_6680
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3148
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_6682 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'glb_6682
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_6684 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8851''45'magma_6684
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3164
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_6686 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'45''8804'_6686
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoid
d_'8851''45'monoid_6688 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8851''45'monoid_6688
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3176
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_6690 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'691''45''8804'_6690
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_6692 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8851''45'mono'737''45''8804'_6692
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3372
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_6694 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_6694
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_6696 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
d_'8851''45'selectiveMagma_6696
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3172
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_6698 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8851''45'semigroup_6698
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3166
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_6700 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_6700 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-zero
d_'8851''45'zero_6702 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_6702
  = let v0 = d_'8852''45'operator_6522 in
    coe
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_166
                      v0 v1 v3 (coe v2 v3)))
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_160
                      v0 v3 v1 (coe v2 v3)))))
-- Data.Integer.Properties.⊓-⊔-properties.⊓-zeroʳ
d_'8851''45'zero'691'_6704 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'691'_6704 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊓-zeroˡ
d_'8851''45'zero'737'_6706 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'737'_6706 = erased
-- Data.Integer.Properties.⊓-⊔-properties.⊔-⊓-absorptive
d_'8852''45''8851''45'absorptive_6708 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45''8851''45'absorptive_6708
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'absorptive_3338
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_6712 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8851''45'isSemilattice_6712
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_616
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_6714 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_6714
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8851''45'operator_6520 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_618
            (coe v0) (coe v1)))
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-⊔-distributiveLattice
d_'8851''45''8852''45'distributiveLattice_6716 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
d_'8851''45''8852''45'distributiveLattice_6716
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'distributiveLattice_822
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-⊔-isDistributiveLattice
d_'8851''45''8852''45'isDistributiveLattice_6718 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_'8851''45''8852''45'isDistributiveLattice_6718
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isDistributiveLattice_812
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-⊔-isLattice
d_'8851''45''8852''45'isLattice_6720 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8851''45''8852''45'isLattice_6720
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isLattice_810
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-⊔-lattice
d_'8851''45''8852''45'lattice_6722 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8851''45''8852''45'lattice_6722
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'lattice_818
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_6724 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8851''45'isSemilattice_6724
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_616
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_6726 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_6726
  = let v0 = d_'8804''45'totalPreorder_2920 in
    coe
      (let v1 = d_'8852''45'operator_6522 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_618
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊔-⊓-distributiveLattice
d_'8852''45''8851''45'distributiveLattice_6728 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
d_'8852''45''8851''45'distributiveLattice_6728
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'distributiveLattice_820
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊔-⊓-isDistributiveLattice
d_'8852''45''8851''45'isDistributiveLattice_6730 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_'8852''45''8851''45'isDistributiveLattice_6730
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isDistributiveLattice_814
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊔-⊓-isLattice
d_'8852''45''8851''45'isLattice_6732 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8852''45''8851''45'isLattice_6732
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isLattice_808
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.⊓-⊔-latticeProperties.⊔-⊓-lattice
d_'8852''45''8851''45'lattice_6734 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8852''45''8851''45'lattice_6734
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'lattice_816
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520) (coe d_'8852''45'operator_6522)
-- Data.Integer.Properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_6742 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8852'_6742 = erased
-- Data.Integer.Properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_6752 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8851'_6752 = erased
-- Data.Integer.Properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_6762 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8851'_6762 = erased
-- Data.Integer.Properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_6772 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
   MAlonzo.Code.Data.Integer.Base.T__'8804'__26) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8852'_6772 = erased
-- Data.Integer.Properties.mono-<-distrib-⊓
d_mono'45''60''45'distrib'45''8851'_6782 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''60''45'distrib'45''8851'_6782 = erased
-- Data.Integer.Properties.mono-<-distrib-⊔
d_mono'45''60''45'distrib'45''8852'_6830 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''60''45'distrib'45''8852'_6830 = erased
-- Data.Integer.Properties.antimono-<-distrib-⊔
d_antimono'45''60''45'distrib'45''8852'_6878 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''60''45'distrib'45''8852'_6878 = erased
-- Data.Integer.Properties.antimono-<-distrib-⊓
d_antimono'45''60''45'distrib'45''8851'_6926 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
   MAlonzo.Code.Data.Integer.Base.T__'60'__50) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''60''45'distrib'45''8851'_6926 = erased
-- Data.Integer.Properties.neg-distrib-⊔-⊓
d_neg'45'distrib'45''8852''45''8851'_6972 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'45''8852''45''8851'_6972 = erased
-- Data.Integer.Properties.neg-distrib-⊓-⊔
d_neg'45'distrib'45''8851''45''8852'_6978 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'45''8851''45''8852'_6978 = erased
-- Data.Integer.Properties.*-distribˡ-⊓-nonNeg
d_'42''45'distrib'737''45''8851''45'nonNeg_6988 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8851''45'nonNeg_6988 = erased
-- Data.Integer.Properties.*-distribʳ-⊓-nonNeg
d_'42''45'distrib'691''45''8851''45'nonNeg_7004 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8851''45'nonNeg_7004 = erased
-- Data.Integer.Properties.*-distribˡ-⊓-nonPos
d_'42''45'distrib'737''45''8851''45'nonPos_7020 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8851''45'nonPos_7020 = erased
-- Data.Integer.Properties.*-distribʳ-⊓-nonPos
d_'42''45'distrib'691''45''8851''45'nonPos_7036 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8851''45'nonPos_7036 = erased
-- Data.Integer.Properties.*-distribˡ-⊔-nonNeg
d_'42''45'distrib'737''45''8852''45'nonNeg_7052 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8852''45'nonNeg_7052 = erased
-- Data.Integer.Properties.*-distribʳ-⊔-nonNeg
d_'42''45'distrib'691''45''8852''45'nonNeg_7068 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8852''45'nonNeg_7068 = erased
-- Data.Integer.Properties.*-distribˡ-⊔-nonPos
d_'42''45'distrib'737''45''8852''45'nonPos_7084 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8852''45'nonPos_7084 = erased
-- Data.Integer.Properties.*-distribʳ-⊔-nonPos
d_'42''45'distrib'691''45''8852''45'nonPos_7100 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8852''45'nonPos_7100 = erased
-- Data.Integer.Properties.neg-mono-<->
d_neg'45'mono'45''60''45''62'_7108 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_neg'45'mono'45''60''45''62'_7108 = coe d_neg'45'mono'45''60'_3410
-- Data.Integer.Properties.neg-mono-≤-≥
d_neg'45'mono'45''8804''45''8805'_7110 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_neg'45'mono'45''8804''45''8805'_7110 v0 v1 v2
  = coe du_neg'45'mono'45''8804'_3380 v1 v2
-- Data.Integer.Properties.*-monoʳ-≤-non-neg
d_'42''45'mono'691''45''8804''45'non'45'neg_7112 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'non'45'neg_7112 v0 v1 v2 v3 v4
  = coe du_'42''45'mono'691''45''8804''45'nonNeg_6120 v0 v2 v3 v4
-- Data.Integer.Properties.*-monoˡ-≤-non-neg
d_'42''45'mono'737''45''8804''45'non'45'neg_7114 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'non'45'neg_7114 v0 v1 v2 v3
  = coe du_'42''45'mono'737''45''8804''45'nonNeg_6162 v0 v2 v3
-- Data.Integer.Properties.*-cancelˡ-<-non-neg
d_'42''45'cancel'737''45''60''45'non'45'neg_7116 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'737''45''60''45'non'45'neg_7116 v0 v1 v2 v3 v4
  = coe du_'42''45'cancel'737''45''60''45'nonNeg_6332 v0 v1 v2 v4
-- Data.Integer.Properties.*-cancelʳ-<-non-neg
d_'42''45'cancel'691''45''60''45'non'45'neg_7118 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'42''45'cancel'691''45''60''45'non'45'neg_7118 v0 v1 v2 v3
  = coe du_'42''45'cancel'691''45''60''45'nonNeg_6370 v0 v1 v2
-- Data.Integer.Properties.m≤n⇒m⊓n≡m
d_m'8804'n'8658'm'8851'n'8801'm_7120 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8851'n'8801'm_7120 = erased
-- Data.Integer.Properties.m⊓n≡m⇒m≤n
d_m'8851'n'8801'm'8658'm'8804'n_7122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8851'n'8801'm'8658'm'8804'n_7122
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520)
-- Data.Integer.Properties.m≥n⇒m⊓n≡n
d_m'8805'n'8658'm'8851'n'8801'n_7124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8805'n'8658'm'8851'n'8801'n_7124 = erased
-- Data.Integer.Properties.m⊓n≡n⇒m≥n
d_m'8851'n'8801'n'8658'm'8805'n_7126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8851'n'8801'n'8658'm'8805'n_7126
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520)
-- Data.Integer.Properties.m⊓n≤n
d_m'8851'n'8804'n_7128 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8851'n'8804'n_7128
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520)
-- Data.Integer.Properties.m⊓n≤m
d_m'8851'n'8804'm_7130 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8851'n'8804'm_7130
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe d_'8804''45'totalPreorder_2920)
      (coe d_'8851''45'operator_6520)
-- Data.Integer.Properties.m≤n⇒m⊔n≡n
d_m'8804'n'8658'm'8852'n'8801'n_7132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8852'n'8801'n_7132 = erased
-- Data.Integer.Properties.m⊔n≡n⇒m≤n
d_m'8852'n'8801'n'8658'm'8804'n_7134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8852'n'8801'n'8658'm'8804'n_7134
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2920))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_6522))
-- Data.Integer.Properties.m≥n⇒m⊔n≡m
d_m'8805'n'8658'm'8852'n'8801'm_7136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8805'n'8658'm'8852'n'8801'm_7136 = erased
-- Data.Integer.Properties.m⊔n≡m⇒m≥n
d_m'8852'n'8801'm'8658'm'8805'n_7138 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8852'n'8801'm'8658'm'8805'n_7138
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2920))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_6522))
-- Data.Integer.Properties.m≤m⊔n
d_m'8804'm'8852'n_7140 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'm'8852'n_7140
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2920))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_6522))
-- Data.Integer.Properties.n≤m⊔n
d_n'8804'm'8852'n_7142 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_n'8804'm'8852'n_7142
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2920))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_6522))
-- Data.Integer.Properties.+-pos-monoʳ-≤
d_'43''45'pos'45'mono'691''45''8804'_7146 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'pos'45'mono'691''45''8804'_7146 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
        -> coe
             d_'8854''45'mono'691''45''8805''45''8804'_3830 (coe v0)
             (coe subInt (coe (0 :: Integer)) (coe v1))
             (coe subInt (coe (0 :: Integer)) (coe v2))
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe
             du_'8804''45'trans_2838
             (coe
                d_m'8854'n'8804'm_3722 (coe v0)
                (coe subInt (coe (0 :: Integer)) (coe v1)))
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0)))
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
        -> coe
             MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
                v0 v1 v2 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.+-neg-monoʳ-≤
d_'43''45'neg'45'mono'691''45''8804'_7162 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''45'neg'45'mono'691''45''8804'_7162 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34 v6
        -> let v7 = subInt (coe (-1 :: Integer)) (coe v1) in
           coe
             (let v8 = subInt (coe (-1 :: Integer)) (coe v2) in
              coe
                (coe
                   MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
                      (addInt (coe (1 :: Integer)) (coe v0)) v8 v7 v6)))
      MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40
        -> coe
             du_'8804''45'trans_2838
             (coe
                MAlonzo.Code.Data.Integer.Base.C_'45''8804''45'_34
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                   (coe addInt (coe (1 :: Integer)) (coe v0))))
             (coe
                d_'45'1'43'm'8804'n'8854'm_3802
                (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48 v6
        -> coe
             d_'8854''45'mono'737''45''8804'_3858
             (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1) (coe v2)
             (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Properties.n≮n
d_n'8814'n_7176 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8814'n_7176 = erased
-- Data.Integer.Properties.∣n∣≡0⇒n≡0
d_'8739'n'8739''8801'0'8658'n'8801'0_7178 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'n'8739''8801'0'8658'n'8801'0_7178 = erased
-- Data.Integer.Properties.∣-n∣≡∣n∣
d_'8739''45'n'8739''8801''8739'n'8739'_7180 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45'n'8739''8801''8739'n'8739'_7180 = erased
-- Data.Integer.Properties.0≤n⇒+∣n∣≡n
d_0'8804'n'8658''43''8739'n'8739''8801'n_7182 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8804'n'8658''43''8739'n'8739''8801'n_7182 = erased
-- Data.Integer.Properties.+∣n∣≡n⇒0≤n
d_'43''8739'n'8739''8801'n'8658'0'8804'n_7184 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'43''8739'n'8739''8801'n'8658'0'8804'n_7184 v0 v1
  = coe du_'43''8739'i'8739''8801'i'8658'0'8804'i_3934
-- Data.Integer.Properties.+∣n∣≡n⊎+∣n∣≡-n
d_'43''8739'n'8739''8801'n'8846''43''8739'n'8739''8801''45'n_7186 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'43''8739'n'8739''8801'n'8846''43''8739'n'8739''8801''45'n_7186
  = coe
      d_'43''8739'i'8739''8801'i'8846''43''8739'i'8739''8801''45'i_3940
-- Data.Integer.Properties.∣m+n∣≤∣m∣+∣n∣
d_'8739'm'43'n'8739''8804''8739'm'8739''43''8739'n'8739'_7188 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'43'n'8739''8804''8739'm'8739''43''8739'n'8739'_7188
  = coe d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3970
-- Data.Integer.Properties.∣m-n∣≤∣m∣+∣n∣
d_'8739'm'45'n'8739''8804''8739'm'8739''43''8739'n'8739'_7190 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'45'n'8739''8804''8739'm'8739''43''8739'n'8739'_7190
  = coe d_'8739'i'45'j'8739''8804''8739'i'8739''43''8739'j'8739'_4008
-- Data.Integer.Properties.signₙ◃∣n∣≡n
d_sign'8345''9667''8739'n'8739''8801'n_7192 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sign'8345''9667''8739'n'8739''8801'n_7192 = erased
-- Data.Integer.Properties.◃-≡
d_'9667''45''8801'_7194 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9667''45''8801'_7194 = erased
-- Data.Integer.Properties.∣m-n∣≡∣n-m∣
d_'8739'm'45'n'8739''8801''8739'n'45'm'8739'_7196 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'45'n'8739''8801''8739'n'45'm'8739'_7196 = erased
-- Data.Integer.Properties.m≡n⇒m-n≡0
d_m'8801'n'8658'm'45'n'8801'0_7198 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8801'n'8658'm'45'n'8801'0_7198 = erased
-- Data.Integer.Properties.m-n≡0⇒m≡n
d_m'45'n'8801'0'8658'm'8801'n_7200 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'45'n'8801'0'8658'm'8801'n_7200 = erased
-- Data.Integer.Properties.≤-steps
d_'8804''45'steps_7202 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'steps_7202 v0 v1 v2 v3 v4
  = coe du_i'8804'j'8658'i'8804'k'43'j_4654 v0 v1 v2 v4
-- Data.Integer.Properties.≤-steps-neg
d_'8804''45'steps'45'neg_7204 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'steps'45'neg_7204 v0 v1 v2 v3 v4
  = coe du_i'8804'j'8658'i'45'k'8804'j_4922 v0 v2 v4
-- Data.Integer.Properties.≤-step
d_'8804''45'step_7206 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'step_7206 = coe d_i'8804'j'8658'i'8804'1'43'j_5018
-- Data.Integer.Properties.≤-step-neg
d_'8804''45'step'45'neg_7208 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8804''45'step'45'neg_7208 v0 v1 v2
  = coe du_i'8804'j'8658'pred'91'i'93''8804'j_5186 v2
-- Data.Integer.Properties.m≤n⇒m-n≤0
d_m'8804'n'8658'm'45'n'8804'0_7210 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'n'8658'm'45'n'8804'0_7210
  = coe d_i'8804'j'8658'i'45'j'8804'0_4956
-- Data.Integer.Properties.m-n≤0⇒m≤n
d_m'45'n'8804'0'8658'm'8804'n_7212 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'45'n'8804'0'8658'm'8804'n_7212
  = coe d_i'45'j'8804'0'8658'i'8804'j_4982
-- Data.Integer.Properties.m≤n⇒0≤n-m
d_m'8804'n'8658'0'8804'n'45'm_7214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'n'8658'0'8804'n'45'm_7214
  = coe d_i'8804'j'8658'0'8804'j'45'i_4994
-- Data.Integer.Properties.0≤n-m⇒m≤n
d_0'8804'n'45'm'8658'm'8804'n_7216 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_0'8804'n'45'm'8658'm'8804'n_7216
  = coe d_0'8804'i'45'j'8658'j'8804'i_5006
-- Data.Integer.Properties.n≤1+n
d_n'8804'1'43'n_7218 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_n'8804'1'43'n_7218 = coe d_i'8804'suc'91'i'93'_5022
-- Data.Integer.Properties.n≢1+n
d_n'8802'1'43'n_7220 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'1'43'n_7220 = erased
-- Data.Integer.Properties.m≤pred[n]⇒m<n
d_m'8804'pred'91'n'93''8658'm'60'n_7222 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_m'8804'pred'91'n'93''8658'm'60'n_7222 v0 v1 v2
  = coe du_i'8804'pred'91'j'93''8658'i'60'j_5164 v1 v2
-- Data.Integer.Properties.m<n⇒m≤pred[n]
d_m'60'n'8658'm'8804'pred'91'n'93'_7224 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'60'n'8658'm'8804'pred'91'n'93'_7224 v0 v1 v2
  = coe du_i'60'j'8658'i'8804'pred'91'j'93'_5174 v1 v2
-- Data.Integer.Properties.-1*n≡-n
d_'45'1'42'n'8801''45'n_7226 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45'1'42'n'8801''45'n_7226 = erased
-- Data.Integer.Properties.m*n≡0⇒m≡0∨n≡0
d_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_7228 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_7228 v0 v1 v2
  = coe du_i'42'j'8801'0'8658'i'8801'0'8744'j'8801'0_5846 v0
-- Data.Integer.Properties.∣m*n∣≡∣m∣*∣n∣
d_'8739'm'42'n'8739''8801''8739'm'8739''42''8739'n'8739'_7230 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'42'n'8739''8801''8739'm'8739''42''8739'n'8739'_7230
  = erased
-- Data.Integer.Properties.n≤m+n
d_n'8804'm'43'n_7234 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_n'8804'm'43'n_7234 v0 v1
  = coe du_i'8804'j'43'i_4668 (coe v0) (coe v1)
-- Data.Integer.Properties.m≤m+n
d_m'8804'm'43'n_7242 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'm'43'n_7242 v0 v1
  = coe du_i'8804'i'43'j_4680 (coe v0) (coe v1)
-- Data.Integer.Properties.m-n≤m
d_m'45'n'8804'm_7252 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'45'n'8804'm_7252 v0 v1
  = coe du_i'45'j'8804'i_4950 (coe v0) (coe v1)
-- Data.Integer.Properties.*-monoʳ-≤-pos
d_'42''45'mono'691''45''8804''45'pos_7262 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'pos_7262 v0 v1 v2
  = coe
      du_'42''45'mono'691''45''8804''45'nonNeg_6120
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1) (coe v2)
-- Data.Integer.Properties.*-monoˡ-≤-pos
d_'42''45'mono'737''45''8804''45'pos_7270 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'pos_7270 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''8804''45'nonNeg_6162
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1) (coe v2)
-- Data.Integer.Properties.*-monoˡ-≤-neg
d_'42''45'mono'737''45''8804''45'neg_7278 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'737''45''8804''45'neg_7278 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''8804''45'nonPos_6230
      (coe subInt (coe (-1 :: Integer)) (coe v0)) (coe v1) (coe v2)
-- Data.Integer.Properties.*-monoʳ-≤-neg
d_'42''45'mono'691''45''8804''45'neg_7286 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'42''45'mono'691''45''8804''45'neg_7286 v0 v1 v2
  = coe
      du_'42''45'mono'691''45''8804''45'nonPos_6258
      (coe subInt (coe (-1 :: Integer)) (coe v0)) (coe v1) (coe v2)
-- Data.Integer.Properties.pos-+-commute
d_pos'45''43''45'commute_7290 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pos'45''43''45'commute_7290 = erased
-- Data.Integer.Properties.abs-*-commute
d_abs'45''42''45'commute_7292 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abs'45''42''45'commute_7292 = erased
-- Data.Integer.Properties.pos-distrib-*
d_pos'45'distrib'45''42'_7298 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pos'45'distrib'45''42'_7298 = erased
-- Data.Integer.Properties.+-isAbelianGroup
d_'43''45'isAbelianGroup_7304 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_7304
  = coe d_'43''45'0'45'isAbelianGroup_4518
