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

module MAlonzo.Code.Data.Bool.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Properties.BooleanAlgebra
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Bool.Properties._._Absorbs_
d__Absorbs__8 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__Absorbs__8 = erased
-- Data.Bool.Properties._._DistributesOver_
d__DistributesOver__10 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__DistributesOver__10 = erased
-- Data.Bool.Properties._._DistributesOverʳ_
d__DistributesOver'691'__12 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__DistributesOver'691'__12 = erased
-- Data.Bool.Properties._._DistributesOverˡ_
d__DistributesOver'737'__14 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__DistributesOver'737'__14 = erased
-- Data.Bool.Properties._._IdempotentOn_
d__IdempotentOn__16 :: (Bool -> Bool -> Bool) -> Bool -> ()
d__IdempotentOn__16 = erased
-- Data.Bool.Properties._._MiddleFourExchange_
d__MiddleFourExchange__18 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d__MiddleFourExchange__18 = erased
-- Data.Bool.Properties._.Absorptive
d_Absorptive_20 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_Absorptive_20 = erased
-- Data.Bool.Properties._.AlmostCancellative
d_AlmostCancellative_22 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_AlmostCancellative_22 = erased
-- Data.Bool.Properties._.AlmostLeftCancellative
d_AlmostLeftCancellative_24 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_AlmostLeftCancellative_24 = erased
-- Data.Bool.Properties._.AlmostRightCancellative
d_AlmostRightCancellative_26 ::
  Bool -> (Bool -> Bool -> Bool) -> ()
d_AlmostRightCancellative_26 = erased
-- Data.Bool.Properties._.Alternative
d_Alternative_28 :: (Bool -> Bool -> Bool) -> ()
d_Alternative_28 = erased
-- Data.Bool.Properties._.Associative
d_Associative_30 :: (Bool -> Bool -> Bool) -> ()
d_Associative_30 = erased
-- Data.Bool.Properties._.Cancellative
d_Cancellative_32 :: (Bool -> Bool -> Bool) -> ()
d_Cancellative_32 = erased
-- Data.Bool.Properties._.Commutative
d_Commutative_34 :: (Bool -> Bool -> Bool) -> ()
d_Commutative_34 = erased
-- Data.Bool.Properties._.Congruent₁
d_Congruent'8321'_36 :: (Bool -> Bool) -> ()
d_Congruent'8321'_36 = erased
-- Data.Bool.Properties._.Congruent₂
d_Congruent'8322'_38 :: (Bool -> Bool -> Bool) -> ()
d_Congruent'8322'_38 = erased
-- Data.Bool.Properties._.Conical
d_Conical_40 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_Conical_40 = erased
-- Data.Bool.Properties._.Flexible
d_Flexible_42 :: (Bool -> Bool -> Bool) -> ()
d_Flexible_42 = erased
-- Data.Bool.Properties._.Idempotent
d_Idempotent_44 :: (Bool -> Bool -> Bool) -> ()
d_Idempotent_44 = erased
-- Data.Bool.Properties._.IdempotentFun
d_IdempotentFun_46 :: (Bool -> Bool) -> ()
d_IdempotentFun_46 = erased
-- Data.Bool.Properties._.Identical
d_Identical_48 :: (Bool -> Bool -> Bool) -> ()
d_Identical_48 = erased
-- Data.Bool.Properties._.Identity
d_Identity_50 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_Identity_50 = erased
-- Data.Bool.Properties._.Interchangable
d_Interchangable_52 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_Interchangable_52 = erased
-- Data.Bool.Properties._.Inverse
d_Inverse_54 ::
  Bool -> (Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_Inverse_54 = erased
-- Data.Bool.Properties._.Invertible
d_Invertible_56 :: Bool -> (Bool -> Bool -> Bool) -> Bool -> ()
d_Invertible_56 = erased
-- Data.Bool.Properties._.Involutive
d_Involutive_58 :: (Bool -> Bool) -> ()
d_Involutive_58 = erased
-- Data.Bool.Properties._.LeftAlternative
d_LeftAlternative_60 :: (Bool -> Bool -> Bool) -> ()
d_LeftAlternative_60 = erased
-- Data.Bool.Properties._.LeftBol
d_LeftBol_62 :: (Bool -> Bool -> Bool) -> ()
d_LeftBol_62 = erased
-- Data.Bool.Properties._.LeftCancellative
d_LeftCancellative_64 :: (Bool -> Bool -> Bool) -> ()
d_LeftCancellative_64 = erased
-- Data.Bool.Properties._.LeftCongruent
d_LeftCongruent_66 :: (Bool -> Bool -> Bool) -> ()
d_LeftCongruent_66 = erased
-- Data.Bool.Properties._.LeftConical
d_LeftConical_68 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_LeftConical_68 = erased
-- Data.Bool.Properties._.LeftDivides
d_LeftDivides_70 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_LeftDivides_70 = erased
-- Data.Bool.Properties._.LeftDividesʳ
d_LeftDivides'691'_72 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_LeftDivides'691'_72 = erased
-- Data.Bool.Properties._.LeftDividesˡ
d_LeftDivides'737'_74 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_LeftDivides'737'_74 = erased
-- Data.Bool.Properties._.LeftIdentity
d_LeftIdentity_76 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_LeftIdentity_76 = erased
-- Data.Bool.Properties._.LeftInverse
d_LeftInverse_78 ::
  Bool -> (Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_LeftInverse_78 = erased
-- Data.Bool.Properties._.LeftInvertible
d_LeftInvertible_80 :: Bool -> (Bool -> Bool -> Bool) -> Bool -> ()
d_LeftInvertible_80 = erased
-- Data.Bool.Properties._.LeftSemimedial
d_LeftSemimedial_82 :: (Bool -> Bool -> Bool) -> ()
d_LeftSemimedial_82 = erased
-- Data.Bool.Properties._.LeftZero
d_LeftZero_84 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_LeftZero_84 = erased
-- Data.Bool.Properties._.Medial
d_Medial_86 :: (Bool -> Bool -> Bool) -> ()
d_Medial_86 = erased
-- Data.Bool.Properties._.MiddleBol
d_MiddleBol_88 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_MiddleBol_88 = erased
-- Data.Bool.Properties._.RightAlternative
d_RightAlternative_90 :: (Bool -> Bool -> Bool) -> ()
d_RightAlternative_90 = erased
-- Data.Bool.Properties._.RightBol
d_RightBol_92 :: (Bool -> Bool -> Bool) -> ()
d_RightBol_92 = erased
-- Data.Bool.Properties._.RightCancellative
d_RightCancellative_94 :: (Bool -> Bool -> Bool) -> ()
d_RightCancellative_94 = erased
-- Data.Bool.Properties._.RightCongruent
d_RightCongruent_96 :: (Bool -> Bool -> Bool) -> ()
d_RightCongruent_96 = erased
-- Data.Bool.Properties._.RightConical
d_RightConical_98 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_RightConical_98 = erased
-- Data.Bool.Properties._.RightDivides
d_RightDivides_100 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_RightDivides_100 = erased
-- Data.Bool.Properties._.RightDividesʳ
d_RightDivides'691'_102 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_RightDivides'691'_102 = erased
-- Data.Bool.Properties._.RightDividesˡ
d_RightDivides'737'_104 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_RightDivides'737'_104 = erased
-- Data.Bool.Properties._.RightIdentity
d_RightIdentity_106 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_RightIdentity_106 = erased
-- Data.Bool.Properties._.RightInverse
d_RightInverse_108 ::
  Bool -> (Bool -> Bool) -> (Bool -> Bool -> Bool) -> ()
d_RightInverse_108 = erased
-- Data.Bool.Properties._.RightInvertible
d_RightInvertible_110 ::
  Bool -> (Bool -> Bool -> Bool) -> Bool -> ()
d_RightInvertible_110 = erased
-- Data.Bool.Properties._.RightSemimedial
d_RightSemimedial_112 :: (Bool -> Bool -> Bool) -> ()
d_RightSemimedial_112 = erased
-- Data.Bool.Properties._.RightZero
d_RightZero_114 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_RightZero_114 = erased
-- Data.Bool.Properties._.Selective
d_Selective_116 :: (Bool -> Bool -> Bool) -> ()
d_Selective_116 = erased
-- Data.Bool.Properties._.SelfInverse
d_SelfInverse_118 :: (Bool -> Bool) -> ()
d_SelfInverse_118 = erased
-- Data.Bool.Properties._.Semimedial
d_Semimedial_120 :: (Bool -> Bool -> Bool) -> ()
d_Semimedial_120 = erased
-- Data.Bool.Properties._.StarDestructive
d_StarDestructive_122 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> ()
d_StarDestructive_122 = erased
-- Data.Bool.Properties._.StarExpansive
d_StarExpansive_124 ::
  Bool ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> ()
d_StarExpansive_124 = erased
-- Data.Bool.Properties._.StarLeftDestructive
d_StarLeftDestructive_126 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> ()
d_StarLeftDestructive_126 = erased
-- Data.Bool.Properties._.StarLeftExpansive
d_StarLeftExpansive_128 ::
  Bool ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> ()
d_StarLeftExpansive_128 = erased
-- Data.Bool.Properties._.StarRightDestructive
d_StarRightDestructive_130 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> ()
d_StarRightDestructive_130 = erased
-- Data.Bool.Properties._.StarRightExpansive
d_StarRightExpansive_132 ::
  Bool ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> ()
d_StarRightExpansive_132 = erased
-- Data.Bool.Properties._.Zero
d_Zero_134 :: Bool -> (Bool -> Bool -> Bool) -> ()
d_Zero_134 = erased
-- Data.Bool.Properties._.IsAbelianGroup
d_IsAbelianGroup_138 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsAlternativeMagma
d_IsAlternativeMagma_142 a0 = ()
-- Data.Bool.Properties._.IsBand
d_IsBand_146 a0 = ()
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_150 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsCommutativeBand
d_IsCommutativeBand_154 a0 = ()
-- Data.Bool.Properties._.IsCommutativeMagma
d_IsCommutativeMagma_158 a0 = ()
-- Data.Bool.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_162 a0 a1 = ()
-- Data.Bool.Properties._.IsCommutativeRing
d_IsCommutativeRing_166 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_170 a0 = ()
-- Data.Bool.Properties._.IsCommutativeSemiring
d_IsCommutativeSemiring_174 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_178 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsFlexibleMagma
d_IsFlexibleMagma_182 a0 = ()
-- Data.Bool.Properties._.IsGroup
d_IsGroup_186 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_190 a0 a1 = ()
-- Data.Bool.Properties._.IsIdempotentMagma
d_IsIdempotentMagma_194 a0 = ()
-- Data.Bool.Properties._.IsIdempotentMonoid
d_IsIdempotentMonoid_198 a0 a1 = ()
-- Data.Bool.Properties._.IsIdempotentSemiring
d_IsIdempotentSemiring_202 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsInvertibleMagma
d_IsInvertibleMagma_206 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_210 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsKleeneAlgebra
d_IsKleeneAlgebra_214 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsLeftBolLoop
d_IsLeftBolLoop_218 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsLoop
d_IsLoop_222 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsMagma
d_IsMagma_226 a0 = ()
-- Data.Bool.Properties._.IsMedialMagma
d_IsMedialMagma_230 a0 = ()
-- Data.Bool.Properties._.IsMiddleBolLoop
d_IsMiddleBolLoop_234 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsMonoid
d_IsMonoid_238 a0 a1 = ()
-- Data.Bool.Properties._.IsMoufangLoop
d_IsMoufangLoop_242 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsNearSemiring
d_IsNearSemiring_246 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsNearring
d_IsNearring_250 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsNonAssociativeRing
d_IsNonAssociativeRing_254 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsQuasigroup
d_IsQuasigroup_258 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsQuasiring
d_IsQuasiring_262 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsRightBolLoop
d_IsRightBolLoop_266 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsRing
d_IsRing_270 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsRingWithoutOne
d_IsRingWithoutOne_274 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsSelectiveMagma
d_IsSelectiveMagma_278 a0 = ()
-- Data.Bool.Properties._.IsSemigroup
d_IsSemigroup_282 a0 = ()
-- Data.Bool.Properties._.IsSemimedialMagma
d_IsSemimedialMagma_286 a0 = ()
-- Data.Bool.Properties._.IsSemiring
d_IsSemiring_290 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_294 a0 a1 a2 a3 = ()
-- Data.Bool.Properties._.IsSemiringWithoutOne
d_IsSemiringWithoutOne_298 a0 a1 a2 = ()
-- Data.Bool.Properties._.IsSuccessorSet
d_IsSuccessorSet_302 a0 a1 = ()
-- Data.Bool.Properties._.IsUnitalMagma
d_IsUnitalMagma_306 a0 a1 = ()
-- Data.Bool.Properties._.IsAbelianGroup._//_
d__'47''47'__312 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool -> Bool -> Bool
d__'47''47'__312 v0 ~v1 v2 ~v3 = du__'47''47'__312 v0 v2
du__'47''47'__312 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool -> Bool
du__'47''47'__312 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Bool.Properties._.IsAbelianGroup.assoc
d_assoc_314 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_314 = erased
-- Data.Bool.Properties._.IsAbelianGroup.comm
d_comm_316 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_316 = erased
-- Data.Bool.Properties._.IsAbelianGroup.identity
d_identity_318 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_318 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))
-- Data.Bool.Properties._.IsAbelianGroup.identityʳ
d_identity'691'_320 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_320 = erased
-- Data.Bool.Properties._.IsAbelianGroup.identityˡ
d_identity'737'_322 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_322 = erased
-- Data.Bool.Properties._.IsAbelianGroup.inverse
d_inverse_324 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Bool.Properties._.IsAbelianGroup.inverseʳ
d_inverse'691'_326 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_326 = erased
-- Data.Bool.Properties._.IsAbelianGroup.inverseˡ
d_inverse'737'_328 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_328 = erased
-- Data.Bool.Properties._.IsAbelianGroup.isCommutativeMagma
d_isCommutativeMagma_330 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAbelianGroup.isCommutativeMonoid
d_isCommutativeMonoid_332 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_332 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244 v3
-- Data.Bool.Properties._.IsAbelianGroup.isCommutativeSemigroup
d_isCommutativeSemigroup_334 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAbelianGroup.isEquivalence
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
-- Data.Bool.Properties._.IsAbelianGroup.isGroup
d_isGroup_338 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_338 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)
-- Data.Bool.Properties._.IsAbelianGroup.isInvertibleMagma
d_isInvertibleMagma_340 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAbelianGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_342 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAbelianGroup.isMagma
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
-- Data.Bool.Properties._.IsAbelianGroup.isMonoid
d_isMonoid_346 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_346 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Bool.Properties._.IsAbelianGroup.isPartialEquivalence
d_isPartialEquivalence_348 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAbelianGroup.isSemigroup
d_isSemigroup_350 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_350 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))
-- Data.Bool.Properties._.IsAbelianGroup.isUnitalMagma
d_isUnitalMagma_352 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAbelianGroup.refl
d_refl_354 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_354 = erased
-- Data.Bool.Properties._.IsAbelianGroup.reflexive
d_reflexive_356 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_356 = erased
-- Data.Bool.Properties._.IsAbelianGroup.setoid
d_setoid_358 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAbelianGroup.sym
d_sym_360 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_360 = erased
-- Data.Bool.Properties._.IsAbelianGroup.trans
d_trans_362 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_362 = erased
-- Data.Bool.Properties._.IsAbelianGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_364 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_364 = erased
-- Data.Bool.Properties._.IsAbelianGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_366 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_366 = erased
-- Data.Bool.Properties._.IsAbelianGroup.⁻¹-cong
d_'8315''185''45'cong_368 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_368 = erased
-- Data.Bool.Properties._.IsAbelianGroup.∙-cong
d_'8729''45'cong_370 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_370 = erased
-- Data.Bool.Properties._.IsAbelianGroup.∙-congʳ
d_'8729''45'cong'691'_372 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_372 = erased
-- Data.Bool.Properties._.IsAbelianGroup.∙-congˡ
d_'8729''45'cong'737'_374 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_374 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.alter
d_alter_378 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_378 v0
  = coe MAlonzo.Code.Algebra.Structures.d_alter_300 (coe v0)
-- Data.Bool.Properties._.IsAlternativeMagma.alternativeʳ
d_alternative'691'_380 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'691'_380 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.alternativeˡ
d_alternative'737'_382 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'737'_382 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.isEquivalence
d_isEquivalence_384 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_384 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0))
-- Data.Bool.Properties._.IsAlternativeMagma.isMagma
d_isMagma_386 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_386 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0)
-- Data.Bool.Properties._.IsAlternativeMagma.isPartialEquivalence
d_isPartialEquivalence_388 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAlternativeMagma.refl
d_refl_390 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_390 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.reflexive
d_reflexive_392 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_392 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.setoid
d_setoid_394 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsAlternativeMagma.sym
d_sym_396 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_396 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.trans
d_trans_398 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_398 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.∙-cong
d_'8729''45'cong_400 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_400 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.∙-congʳ
d_'8729''45'cong'691'_402 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_402 = erased
-- Data.Bool.Properties._.IsAlternativeMagma.∙-congˡ
d_'8729''45'cong'737'_404 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_404 = erased
-- Data.Bool.Properties._.IsBand.assoc
d_assoc_408 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_408 = erased
-- Data.Bool.Properties._.IsBand.idem
d_idem_410 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_410 = erased
-- Data.Bool.Properties._.IsBand.isEquivalence
d_isEquivalence_412 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_412 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)))
-- Data.Bool.Properties._.IsBand.isMagma
d_isMagma_414 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0))
-- Data.Bool.Properties._.IsBand.isPartialEquivalence
d_isPartialEquivalence_416 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsBand.isSemigroup
d_isSemigroup_418 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_418 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)
-- Data.Bool.Properties._.IsBand.refl
d_refl_420 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_420 = erased
-- Data.Bool.Properties._.IsBand.reflexive
d_reflexive_422 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_422 = erased
-- Data.Bool.Properties._.IsBand.setoid
d_setoid_424 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsBand.sym
d_sym_426 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_426 = erased
-- Data.Bool.Properties._.IsBand.trans
d_trans_428 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_428 = erased
-- Data.Bool.Properties._.IsBand.∙-cong
d_'8729''45'cong_430 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_430 = erased
-- Data.Bool.Properties._.IsBand.∙-congʳ
d_'8729''45'cong'691'_432 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_432 = erased
-- Data.Bool.Properties._.IsBand.∙-congˡ
d_'8729''45'cong'737'_434 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_434 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-assoc
d_'42''45'assoc_438 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_438 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-cancelʳ-nonZero
d_'42''45'cancel'691''45'nonZero_440 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'691''45'nonZero_440 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_442 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45'nonZero_442 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-comm
d_'42''45'comm_444 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_444 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-cong
d_'42''45'cong_446 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_446 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_448 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_448 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_450 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_450 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-identity
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.identityʳ
d_identity'691'_454 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_454 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.identityˡ
d_identity'737'_456 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_456 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_458 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_460 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_462 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-isMagma
d_'42''45'isMagma_464 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-isMonoid
d_'42''45'isMonoid_466 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.*-isSemigroup
d_'42''45'isSemigroup_468 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.assoc
d_assoc_470 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_470 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.comm
d_comm_472 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_472 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.∙-cong
d_'8729''45'cong_474 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_474 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_476 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_476 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_478 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_478 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.identity
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.identityʳ
d_identity'691'_482 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_482 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.identityˡ
d_identity'737'_484 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_484 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_486 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.+-isCommutativeMonoid
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_490 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isMagma
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isMonoid
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isSemigroup
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isUnitalMagma
d_isUnitalMagma_498 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.distrib
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.distribʳ
d_distrib'691'_502 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_502 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.distribˡ
d_distrib'737'_504 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_504 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_506 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_506 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
      (coe v0)
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_508 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isEquivalence
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isNearSemiring
d_isNearSemiring_512 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isPartialEquivalence
d_isPartialEquivalence_514 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isSemiring
d_isSemiring_516 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_516 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutAnnihilatingZero
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_520 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.refl
d_refl_522 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_522 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.reflexive
d_reflexive_524 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_524 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.setoid
d_setoid_526 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.sym
d_sym_528 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_528 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.trans
d_trans_530 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_530 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.zero
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
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.zeroʳ
d_zero'691'_534 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_534 = erased
-- Data.Bool.Properties._.IsCancellativeCommutativeSemiring.zeroˡ
d_zero'737'_536 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_536 = erased
-- Data.Bool.Properties._.IsCommutativeBand.assoc
d_assoc_540 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_540 = erased
-- Data.Bool.Properties._.IsCommutativeBand.comm
d_comm_542 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_542 = erased
-- Data.Bool.Properties._.IsCommutativeBand.idem
d_idem_544 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_544 = erased
-- Data.Bool.Properties._.IsCommutativeBand.isBand
d_isBand_546 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_546 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Data.Bool.Properties._.IsCommutativeBand.isCommutativeMagma
d_isCommutativeMagma_548 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsCommutativeBand.isCommutativeSemigroup
d_isCommutativeSemigroup_550 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_550 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_654 v1
-- Data.Bool.Properties._.IsCommutativeBand.isEquivalence
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
-- Data.Bool.Properties._.IsCommutativeBand.isMagma
d_isMagma_554 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_554 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeBand.isPartialEquivalence
d_isPartialEquivalence_556 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsCommutativeBand.isSemigroup
d_isSemigroup_558 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_558 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Data.Bool.Properties._.IsCommutativeBand.refl
d_refl_560 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_560 = erased
-- Data.Bool.Properties._.IsCommutativeBand.reflexive
d_reflexive_562 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_562 = erased
-- Data.Bool.Properties._.IsCommutativeBand.setoid
d_setoid_564 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsCommutativeBand.sym
d_sym_566 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_566 = erased
-- Data.Bool.Properties._.IsCommutativeBand.trans
d_trans_568 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_568 = erased
-- Data.Bool.Properties._.IsCommutativeBand.∙-cong
d_'8729''45'cong_570 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_570 = erased
-- Data.Bool.Properties._.IsCommutativeBand.∙-congʳ
d_'8729''45'cong'691'_572 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_572 = erased
-- Data.Bool.Properties._.IsCommutativeBand.∙-congˡ
d_'8729''45'cong'737'_574 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_574 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.comm
d_comm_578 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_578 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.isEquivalence
d_isEquivalence_580 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_580 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0))
-- Data.Bool.Properties._.IsCommutativeMagma.isMagma
d_isMagma_582 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_582 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0)
-- Data.Bool.Properties._.IsCommutativeMagma.isPartialEquivalence
d_isPartialEquivalence_584 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsCommutativeMagma.refl
d_refl_586 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_586 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.reflexive
d_reflexive_588 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_588 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.setoid
d_setoid_590 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsCommutativeMagma.sym
d_sym_592 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_592 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.trans
d_trans_594 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_594 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.∙-cong
d_'8729''45'cong_596 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_596 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.∙-congʳ
d_'8729''45'cong'691'_598 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_598 = erased
-- Data.Bool.Properties._.IsCommutativeMagma.∙-congˡ
d_'8729''45'cong'737'_600 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_600 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.assoc
d_assoc_604 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_604 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.comm
d_comm_606 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_606 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.identity
d_identity_608 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_608 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Bool.Properties._.IsCommutativeMonoid.identityʳ
d_identity'691'_610 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_610 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.identityˡ
d_identity'737'_612 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_612 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_614 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_616 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_616 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814 v2
-- Data.Bool.Properties._.IsCommutativeMonoid.isEquivalence
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
-- Data.Bool.Properties._.IsCommutativeMonoid.isMagma
d_isMagma_620 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_620 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_622 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_622 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)
-- Data.Bool.Properties._.IsCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_624 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeMonoid.isSemigroup
d_isSemigroup_626 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_626 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Bool.Properties._.IsCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_628 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeMonoid.refl
d_refl_630 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_630 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.reflexive
d_reflexive_632 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_632 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.setoid
d_setoid_634 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeMonoid.sym
d_sym_636 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_636 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.trans
d_trans_638 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_638 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.∙-cong
d_'8729''45'cong_640 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_640 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_642 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_642 = erased
-- Data.Bool.Properties._.IsCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_644 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_644 = erased
-- Data.Bool.Properties._.IsCommutativeRing._//_
d__'47''47'__648 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> Bool -> Bool
d__'47''47'__648 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__648 v0 v2
du__'47''47'__648 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool -> Bool
du__'47''47'__648 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Bool.Properties._.IsCommutativeRing.*-assoc
d_'42''45'assoc_650 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_650 = erased
-- Data.Bool.Properties._.IsCommutativeRing.*-comm
d_'42''45'comm_652 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_652 = erased
-- Data.Bool.Properties._.IsCommutativeRing.*-cong
d_'42''45'cong_654 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_654 = erased
-- Data.Bool.Properties._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_656 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_656 = erased
-- Data.Bool.Properties._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_658 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_658 = erased
-- Data.Bool.Properties._.IsCommutativeRing.*-identity
d_'42''45'identity_660 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_660 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Bool.Properties._.IsCommutativeRing.identityʳ
d_identity'691'_662 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_662 = erased
-- Data.Bool.Properties._.IsCommutativeRing.identityˡ
d_identity'737'_664 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_664 = erased
-- Data.Bool.Properties._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_666 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_666 v0 v1 v2 v3 ~v4 v5
  = du_isCommutativeMagma_666 v0 v1 v2 v3 v5
du_isCommutativeMagma_666 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_668 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_668 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isCommutativeMonoid_668 v0 v1 v2 v3 v5
du_'42''45'isCommutativeMonoid_668 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_668 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Bool.Properties._.IsCommutativeRing.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_670 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_670 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isCommutativeSemigroup_670 v0 v1 v2 v3 v5
du_'42''45'isCommutativeSemigroup_670 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.*-isMagma
d_'42''45'isMagma_672 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_672 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMagma_672 v0 v1 v2 v3 v5
du_'42''45'isMagma_672 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.*-isMonoid
d_'42''45'isMonoid_674 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_674 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMonoid_674 v0 v1 v2 v3 v5
du_'42''45'isMonoid_674 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_674 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2860 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4))
-- Data.Bool.Properties._.IsCommutativeRing.*-isSemigroup
d_'42''45'isSemigroup_676 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_676 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isSemigroup_676 v0 v1 v2 v3 v5
du_'42''45'isSemigroup_676 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.assoc
d_assoc_678 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_678 = erased
-- Data.Bool.Properties._.IsCommutativeRing.comm
d_comm_680 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_680 = erased
-- Data.Bool.Properties._.IsCommutativeRing.∙-cong
d_'8729''45'cong_682 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_682 = erased
-- Data.Bool.Properties._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_684 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_684 = erased
-- Data.Bool.Properties._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_686 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_686 = erased
-- Data.Bool.Properties._.IsCommutativeRing.identity
d_identity_688 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.identityʳ
d_identity'691'_690 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_690 = erased
-- Data.Bool.Properties._.IsCommutativeRing.identityˡ
d_identity'737'_692 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_692 = erased
-- Data.Bool.Properties._.IsCommutativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_694 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_694 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Bool.Properties._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_696 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isCommutativeMonoid
d_isCommutativeMonoid_698 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_700 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isGroup
d_isGroup_702 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isInvertibleMagma
d_isInvertibleMagma_704 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_706 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isMagma
d_isMagma_708 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isMonoid
d_isMonoid_710 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isSemigroup
d_isSemigroup_712 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isUnitalMagma
d_isUnitalMagma_714 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.⁻¹-cong
d_'8315''185''45'cong_716 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_716 = erased
-- Data.Bool.Properties._.IsCommutativeRing.inverse
d_inverse_718 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.inverseʳ
d_inverse'691'_720 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_720 = erased
-- Data.Bool.Properties._.IsCommutativeRing.inverseˡ
d_inverse'737'_722 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_722 = erased
-- Data.Bool.Properties._.IsCommutativeRing.distrib
d_distrib_724 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_724 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2770
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Bool.Properties._.IsCommutativeRing.distribʳ
d_distrib'691'_726 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_726 = erased
-- Data.Bool.Properties._.IsCommutativeRing.distribˡ
d_distrib'737'_728 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_728 = erased
-- Data.Bool.Properties._.IsCommutativeRing.isCommutativeSemiring
d_isCommutativeSemiring_730 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_730 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018 v0 v1
      v2 v3 v5
-- Data.Bool.Properties._.IsCommutativeRing.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_732 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_732 v0 v1 v2 v3 ~v4 v5
  = du_isCommutativeSemiringWithoutOne_732 v0 v1 v2 v3 v5
du_isCommutativeSemiringWithoutOne_732 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_732 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Bool.Properties._.IsCommutativeRing.isEquivalence
d_isEquivalence_734 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isNearSemiring
d_isNearSemiring_736 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_736 v0 v1 v2 v3 ~v4 v5
  = du_isNearSemiring_736 v0 v1 v2 v3 v5
du_isNearSemiring_736 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isPartialEquivalence
d_isPartialEquivalence_738 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isRing
d_isRing_740 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_isRing_740 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0)
-- Data.Bool.Properties._.IsCommutativeRing.isRingWithoutOne
d_isRingWithoutOne_742 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isSemiring
d_isSemiring_744 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_744 v0 v1 v2 v3 ~v4 v5
  = du_isSemiring_744 v0 v1 v2 v3 v5
du_isSemiring_744 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
du_isSemiring_744 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4))
-- Data.Bool.Properties._.IsCommutativeRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_746 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.isSemiringWithoutOne
d_isSemiringWithoutOne_748 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_748 v0 v1 v2 v3 ~v4 v5
  = du_isSemiringWithoutOne_748 v0 v1 v2 v3 v5
du_isSemiringWithoutOne_748 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.refl
d_refl_750 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_750 = erased
-- Data.Bool.Properties._.IsCommutativeRing.reflexive
d_reflexive_752 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_752 = erased
-- Data.Bool.Properties._.IsCommutativeRing.setoid
d_setoid_754 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.sym
d_sym_756 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_756 = erased
-- Data.Bool.Properties._.IsCommutativeRing.trans
d_trans_758 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_758 = erased
-- Data.Bool.Properties._.IsCommutativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_760 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_760 = erased
-- Data.Bool.Properties._.IsCommutativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_762 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_762 = erased
-- Data.Bool.Properties._.IsCommutativeRing.zero
d_zero_764 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_764 v0 v1 v2 v3 ~v4 v5 = du_zero_764 v0 v1 v2 v3 v5
du_zero_764 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeRing.zeroʳ
d_zero'691'_766 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_766 = erased
-- Data.Bool.Properties._.IsCommutativeRing.zeroˡ
d_zero'737'_768 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_768 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.assoc
d_assoc_772 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_772 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.comm
d_comm_774 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_774 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.isCommutativeMagma
d_isCommutativeMagma_776 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_776 v0 v1
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606 v1
-- Data.Bool.Properties._.IsCommutativeSemigroup.isEquivalence
d_isEquivalence_778 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_778 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemigroup.isMagma
d_isMagma_780 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_780 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemigroup.isPartialEquivalence
d_isPartialEquivalence_782 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_784 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)
-- Data.Bool.Properties._.IsCommutativeSemigroup.refl
d_refl_786 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_786 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.reflexive
d_reflexive_788 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_788 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.setoid
d_setoid_790 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsCommutativeSemigroup.sym
d_sym_792 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_792 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.trans
d_trans_794 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_794 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.∙-cong
d_'8729''45'cong_796 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_796 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.∙-congʳ
d_'8729''45'cong'691'_798 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_798 = erased
-- Data.Bool.Properties._.IsCommutativeSemigroup.∙-congˡ
d_'8729''45'cong'737'_800 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_800 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.*-assoc
d_'42''45'assoc_804 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_804 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.*-comm
d_'42''45'comm_806 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_806 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.*-cong
d_'42''45'cong_808 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_808 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_810 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_810 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_812 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_812 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.*-identity
d_'42''45'identity_814 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_814 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemiring.identityʳ
d_identity'691'_816 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_816 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.identityˡ
d_identity'737'_818 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_818 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_820 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_822 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_822 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      v4
-- Data.Bool.Properties._.IsCommutativeSemiring.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_824 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.*-isMagma
d_'42''45'isMagma_826 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.*-isMonoid
d_'42''45'isMonoid_828 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.*-isSemigroup
d_'42''45'isSemigroup_830 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.assoc
d_assoc_832 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_832 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.comm
d_comm_834 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_834 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.∙-cong
d_'8729''45'cong_836 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_836 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_838 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_838 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_840 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_840 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.identity
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
-- Data.Bool.Properties._.IsCommutativeSemiring.identityʳ
d_identity'691'_844 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_844 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.identityˡ
d_identity'737'_846 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_846 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_848 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_850 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_850 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_852 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.isMagma
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
-- Data.Bool.Properties._.IsCommutativeSemiring.isMonoid
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
-- Data.Bool.Properties._.IsCommutativeSemiring.isSemigroup
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
-- Data.Bool.Properties._.IsCommutativeSemiring.isUnitalMagma
d_isUnitalMagma_860 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.distrib
d_distrib_862 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_862 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Bool.Properties._.IsCommutativeSemiring.distribʳ
d_distrib'691'_864 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_864 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.distribˡ
d_distrib'737'_866 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_866 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_868 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_868 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      v4
-- Data.Bool.Properties._.IsCommutativeSemiring.isEquivalence
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
-- Data.Bool.Properties._.IsCommutativeSemiring.isNearSemiring
d_isNearSemiring_872 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.isPartialEquivalence
d_isPartialEquivalence_874 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.isSemiring
d_isSemiring_876 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_876 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)
-- Data.Bool.Properties._.IsCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_878 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_878 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_880 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.refl
d_refl_882 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_882 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.reflexive
d_reflexive_884 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_884 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.setoid
d_setoid_886 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiring.sym
d_sym_888 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_888 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.trans
d_trans_890 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_890 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.zero
d_zero_892 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_892 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiring.zeroʳ
d_zero'691'_894 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_894 = erased
-- Data.Bool.Properties._.IsCommutativeSemiring.zeroˡ
d_zero'737'_896 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_896 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-assoc
d_'42''45'assoc_900 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_900 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_902 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_902 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-cong
d_'42''45'cong_904 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_904 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_906 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_906 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_908 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_908 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_910 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_912 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_912 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
      v3
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_914 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_916 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.assoc
d_assoc_918 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_918 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.comm
d_comm_920 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_920 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.∙-cong
d_'8729''45'cong_922 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_922 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_924 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_924 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_926 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_926 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.identity
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.identityʳ
d_identity'691'_930 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_930 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.identityˡ
d_identity'737'_932 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_932 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_934 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_936 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_936 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_938 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isMonoid
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.distrib
d_distrib_942 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_942 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1366
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.distribʳ
d_distrib'691'_944 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_944 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.distribˡ
d_distrib'737'_946 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_946 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isEquivalence
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isNearSemiring
d_isNearSemiring_950 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isPartialEquivalence
d_isPartialEquivalence_952 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_954 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_954 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
      (coe v0)
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.refl
d_refl_956 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_956 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.reflexive
d_reflexive_958 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_958 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.setoid
d_setoid_960 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.sym
d_sym_962 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_962 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.trans
d_trans_964 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_964 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.zero
d_zero_966 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_966 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1368
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.zeroʳ
d_zero'691'_968 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_968 = erased
-- Data.Bool.Properties._.IsCommutativeSemiringWithoutOne.zeroˡ
d_zero'737'_970 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_970 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.flex
d_flex_974 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flex_974 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.isEquivalence
d_isEquivalence_976 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_976 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0))
-- Data.Bool.Properties._.IsFlexibleMagma.isMagma
d_isMagma_978 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_978 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0)
-- Data.Bool.Properties._.IsFlexibleMagma.isPartialEquivalence
d_isPartialEquivalence_980 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsFlexibleMagma.refl
d_refl_982 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_982 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.reflexive
d_reflexive_984 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_984 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.setoid
d_setoid_986 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsFlexibleMagma.sym
d_sym_988 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_988 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.trans
d_trans_990 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_990 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.∙-cong
d_'8729''45'cong_992 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_992 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.∙-congʳ
d_'8729''45'cong'691'_994 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_994 = erased
-- Data.Bool.Properties._.IsFlexibleMagma.∙-congˡ
d_'8729''45'cong'737'_996 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_996 = erased
-- Data.Bool.Properties._.IsGroup._-_
d__'45'__1000 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool -> Bool -> Bool
d__'45'__1000 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du__'45'__1142 v0 v2
-- Data.Bool.Properties._.IsGroup._//_
d__'47''47'__1002 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool -> Bool -> Bool
d__'47''47'__1002 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 v0 v2 v4 v5
-- Data.Bool.Properties._.IsGroup._\\_
d__'92''92'__1004 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool -> Bool -> Bool
d__'92''92'__1004 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du__'92''92'__1130 v0 v2 v4 v5
-- Data.Bool.Properties._.IsGroup.assoc
d_assoc_1006 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1006 = erased
-- Data.Bool.Properties._.IsGroup.identity
d_identity_1008 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1008 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Bool.Properties._.IsGroup.identityʳ
d_identity'691'_1010 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1010 = erased
-- Data.Bool.Properties._.IsGroup.identityˡ
d_identity'737'_1012 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1012 = erased
-- Data.Bool.Properties._.IsGroup.inverse
d_inverse_1014 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1014 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1090 (coe v0)
-- Data.Bool.Properties._.IsGroup.inverseʳ
d_inverse'691'_1016 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1016 = erased
-- Data.Bool.Properties._.IsGroup.inverseˡ
d_inverse'737'_1018 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1018 = erased
-- Data.Bool.Properties._.IsGroup.isEquivalence
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
-- Data.Bool.Properties._.IsGroup.isInvertibleMagma
d_isInvertibleMagma_1022 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1022 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160 v3
-- Data.Bool.Properties._.IsGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1024 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_1024 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162 v3
-- Data.Bool.Properties._.IsGroup.isMagma
d_isMagma_1026 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1026 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)))
-- Data.Bool.Properties._.IsGroup.isMonoid
d_isMonoid_1028 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1028 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)
-- Data.Bool.Properties._.IsGroup.isPartialEquivalence
d_isPartialEquivalence_1030 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsGroup.isSemigroup
d_isSemigroup_1032 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1032 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Bool.Properties._.IsGroup.isUnitalMagma
d_isUnitalMagma_1034 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsGroup.refl
d_refl_1036 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1036 = erased
-- Data.Bool.Properties._.IsGroup.reflexive
d_reflexive_1038 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1038 = erased
-- Data.Bool.Properties._.IsGroup.setoid
d_setoid_1040 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsGroup.sym
d_sym_1042 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1042 = erased
-- Data.Bool.Properties._.IsGroup.trans
d_trans_1044 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1044 = erased
-- Data.Bool.Properties._.IsGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_1046 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_1046 = erased
-- Data.Bool.Properties._.IsGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_1048 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_1048 = erased
-- Data.Bool.Properties._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_1050 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1050 = erased
-- Data.Bool.Properties._.IsGroup.∙-cong
d_'8729''45'cong_1052 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1052 = erased
-- Data.Bool.Properties._.IsGroup.∙-congʳ
d_'8729''45'cong'691'_1054 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1054 = erased
-- Data.Bool.Properties._.IsGroup.∙-congˡ
d_'8729''45'cong'737'_1056 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1056 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.assoc
d_assoc_1060 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1060 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.comm
d_comm_1062 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1062 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.idem
d_idem_1064 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1064 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.identity
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.identityʳ
d_identity'691'_1068 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1068 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.identityˡ
d_identity'737'_1070 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1070 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isBand
d_isBand_1072 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isCommutativeBand
d_isCommutativeBand_1074 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1074 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 v2
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_1076 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_1078 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_1078 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0)
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_1080 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isEquivalence
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isIdempotentMonoid
d_isIdempotentMonoid_1084 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1084 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 v2
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isMagma
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isMonoid
d_isMonoid_1088 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1088 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_1090 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isSemigroup
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_1094 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.refl
d_refl_1096 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1096 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.reflexive
d_reflexive_1098 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1098 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.setoid
d_setoid_1100 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.sym
d_sym_1102 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1102 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.trans
d_trans_1104 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1104 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.∙-cong
d_'8729''45'cong_1106 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1106 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_1108 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1108 = erased
-- Data.Bool.Properties._.IsIdempotentCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_1110 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1110 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.idem
d_idem_1114 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1114 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.isEquivalence
d_isEquivalence_1116 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1116 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0))
-- Data.Bool.Properties._.IsIdempotentMagma.isMagma
d_isMagma_1118 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1118 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0)
-- Data.Bool.Properties._.IsIdempotentMagma.isPartialEquivalence
d_isPartialEquivalence_1120 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsIdempotentMagma.refl
d_refl_1122 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1122 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.reflexive
d_reflexive_1124 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1124 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.setoid
d_setoid_1126 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsIdempotentMagma.sym
d_sym_1128 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1128 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.trans
d_trans_1130 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1130 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.∙-cong
d_'8729''45'cong_1132 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1132 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.∙-congʳ
d_'8729''45'cong'691'_1134 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1134 = erased
-- Data.Bool.Properties._.IsIdempotentMagma.∙-congˡ
d_'8729''45'cong'737'_1136 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1136 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.assoc
d_assoc_1140 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1140 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.idem
d_idem_1142 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1142 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.identity
d_identity_1144 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1144 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Bool.Properties._.IsIdempotentMonoid.identityʳ
d_identity'691'_1146 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1146 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.identityˡ
d_identity'737'_1148 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1148 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.isBand
d_isBand_1150 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1150 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isBand_876 v2
-- Data.Bool.Properties._.IsIdempotentMonoid.isEquivalence
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
-- Data.Bool.Properties._.IsIdempotentMonoid.isMagma
d_isMagma_1154 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0)))
-- Data.Bool.Properties._.IsIdempotentMonoid.isMonoid
d_isMonoid_1156 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1156 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0)
-- Data.Bool.Properties._.IsIdempotentMonoid.isPartialEquivalence
d_isPartialEquivalence_1158 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentMonoid.isSemigroup
d_isSemigroup_1160 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1160 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Bool.Properties._.IsIdempotentMonoid.isUnitalMagma
d_isUnitalMagma_1162 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentMonoid.refl
d_refl_1164 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1164 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.reflexive
d_reflexive_1166 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1166 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.setoid
d_setoid_1168 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentMonoid.sym
d_sym_1170 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1170 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.trans
d_trans_1172 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1172 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.∙-cong
d_'8729''45'cong_1174 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1174 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.∙-congʳ
d_'8729''45'cong'691'_1176 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1176 = erased
-- Data.Bool.Properties._.IsIdempotentMonoid.∙-congˡ
d_'8729''45'cong'737'_1178 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1178 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.*-assoc
d_'42''45'assoc_1182 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1182 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.*-cong
d_'42''45'cong_1184 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1184 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.∙-congʳ
d_'8729''45'cong'691'_1186 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1186 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.∙-congˡ
d_'8729''45'cong'737'_1188 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1188 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.*-identity
d_'42''45'identity_1190 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1190 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Bool.Properties._.IsIdempotentSemiring.identityʳ
d_identity'691'_1192 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1192 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.identityˡ
d_identity'737'_1194 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1194 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.*-isMagma
d_'42''45'isMagma_1196 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.*-isMonoid
d_'42''45'isMonoid_1198 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.*-isSemigroup
d_'42''45'isSemigroup_1200 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.assoc
d_assoc_1202 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1202 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.comm
d_comm_1204 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1204 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.∙-cong
d_'8729''45'cong_1206 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1206 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.∙-congʳ
d_'8729''45'cong'691'_1208 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1208 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.∙-congˡ
d_'8729''45'cong'737'_1210 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1210 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.+-idem
d_'43''45'idem_1212 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1212 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.identity
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
-- Data.Bool.Properties._.IsIdempotentSemiring.identityʳ
d_identity'691'_1216 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1216 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.identityˡ
d_identity'737'_1218 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1218 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.isBand
d_isBand_1220 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isCommutativeBand
d_isCommutativeBand_1222 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isCommutativeMagma
d_isCommutativeMagma_1224 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1226 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1226 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Bool.Properties._.IsIdempotentSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_1228 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_1230 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_1230 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
      v4
-- Data.Bool.Properties._.IsIdempotentSemiring.isIdempotentMonoid
d_isIdempotentMonoid_1232 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isMagma
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isMonoid
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isSemigroup
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isUnitalMagma
d_isUnitalMagma_1240 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.distrib
d_distrib_1242 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1242 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Bool.Properties._.IsIdempotentSemiring.distribʳ
d_distrib'691'_1244 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1244 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.distribˡ
d_distrib'737'_1246 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1246 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.isEquivalence
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isNearSemiring
d_isNearSemiring_1250 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isPartialEquivalence
d_isPartialEquivalence_1252 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.isSemiring
d_isSemiring_1254 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_1254 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)
-- Data.Bool.Properties._.IsIdempotentSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1256 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Bool.Properties._.IsIdempotentSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_1258 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.refl
d_refl_1260 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1260 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.reflexive
d_reflexive_1262 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1262 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.setoid
d_setoid_1264 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsIdempotentSemiring.sym
d_sym_1266 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1266 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.trans
d_trans_1268 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1268 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.zero
d_zero_1270 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Bool.Properties._.IsIdempotentSemiring.zeroʳ
d_zero'691'_1272 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1272 = erased
-- Data.Bool.Properties._.IsIdempotentSemiring.zeroˡ
d_zero'737'_1274 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1274 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.inverse
d_inverse_1278 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1278 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_974 (coe v0)
-- Data.Bool.Properties._.IsInvertibleMagma.inverseʳ
d_inverse'691'_1280 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1280 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.inverseˡ
d_inverse'737'_1282 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1282 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.isEquivalence
d_isEquivalence_1284 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1284 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0))
-- Data.Bool.Properties._.IsInvertibleMagma.isMagma
d_isMagma_1286 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1286 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0)
-- Data.Bool.Properties._.IsInvertibleMagma.isPartialEquivalence
d_isPartialEquivalence_1288 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsInvertibleMagma.refl
d_refl_1290 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1290 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.reflexive
d_reflexive_1292 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1292 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.setoid
d_setoid_1294 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsInvertibleMagma.sym
d_sym_1296 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1296 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.trans
d_trans_1298 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1298 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_1300 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1300 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.∙-cong
d_'8729''45'cong_1302 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1302 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.∙-congʳ
d_'8729''45'cong'691'_1304 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1304 = erased
-- Data.Bool.Properties._.IsInvertibleMagma.∙-congˡ
d_'8729''45'cong'737'_1306 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1306 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.identity
d_identity_1310 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1310 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_1026 (coe v0)
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.identityʳ
d_identity'691'_1312 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1312 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.identityˡ
d_identity'737'_1314 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1314 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.inverse
d_inverse_1316 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1316 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_974
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0))
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.inverseʳ
d_inverse'691'_1318 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1318 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.inverseˡ
d_inverse'737'_1320 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1320 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.isEquivalence
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
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_1324 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0)
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.isMagma
d_isMagma_1326 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1326 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_972
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0))
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.isPartialEquivalence
d_isPartialEquivalence_1328 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.isUnitalMagma
d_isUnitalMagma_1330 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1330 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_1064 v3
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.refl
d_refl_1332 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1332 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.reflexive
d_reflexive_1334 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1334 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.setoid
d_setoid_1336 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.sym
d_sym_1338 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1338 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.trans
d_trans_1340 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1340 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.⁻¹-cong
d_'8315''185''45'cong_1342 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1342 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.∙-cong
d_'8729''45'cong_1344 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1344 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.∙-congʳ
d_'8729''45'cong'691'_1346 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1346 = erased
-- Data.Bool.Properties._.IsInvertibleUnitalMagma.∙-congˡ
d_'8729''45'cong'737'_1348 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1348 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.*-assoc
d_'42''45'assoc_1352 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1352 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.*-cong
d_'42''45'cong_1354 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1354 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.∙-congʳ
d_'8729''45'cong'691'_1356 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1356 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.∙-congˡ
d_'8729''45'cong'737'_1358 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1358 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.*-identity
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
-- Data.Bool.Properties._.IsKleeneAlgebra.identityʳ
d_identity'691'_1362 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1362 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.identityˡ
d_identity'737'_1364 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1364 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.*-isMagma
d_'42''45'isMagma_1366 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.*-isMonoid
d_'42''45'isMonoid_1368 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.*-isSemigroup
d_'42''45'isSemigroup_1370 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.assoc
d_assoc_1372 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1372 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.comm
d_comm_1374 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1374 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.∙-cong
d_'8729''45'cong_1376 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1376 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.∙-congʳ
d_'8729''45'cong'691'_1378 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1378 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.∙-congˡ
d_'8729''45'cong'737'_1380 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1380 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.+-idem
d_'43''45'idem_1382 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1382 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.identity
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
-- Data.Bool.Properties._.IsKleeneAlgebra.identityʳ
d_identity'691'_1386 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1386 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.identityˡ
d_identity'737'_1388 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1388 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.isBand
d_isBand_1390 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isCommutativeBand
d_isCommutativeBand_1392 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isCommutativeMagma
d_isCommutativeMagma_1394 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.+-isCommutativeMonoid
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isCommutativeSemigroup
d_isCommutativeSemigroup_1398 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_1400 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isIdempotentMonoid
d_isIdempotentMonoid_1402 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isMagma
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isMonoid
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isSemigroup
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isUnitalMagma
d_isUnitalMagma_1410 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.distrib
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
-- Data.Bool.Properties._.IsKleeneAlgebra.distribʳ
d_distrib'691'_1414 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1414 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.distribˡ
d_distrib'737'_1416 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1416 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.isEquivalence
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_1420 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998
d_isIdempotentSemiring_1420 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
      (coe v0)
-- Data.Bool.Properties._.IsKleeneAlgebra.isNearSemiring
d_isNearSemiring_1422 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isPartialEquivalence
d_isPartialEquivalence_1424 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isSemiring
d_isSemiring_1426 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_1426 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
         (coe v0))
-- Data.Bool.Properties._.IsKleeneAlgebra.isSemiringWithoutAnnihilatingZero
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
-- Data.Bool.Properties._.IsKleeneAlgebra.isSemiringWithoutOne
d_isSemiringWithoutOne_1430 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.refl
d_refl_1432 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1432 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.reflexive
d_reflexive_1434 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1434 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.setoid
d_setoid_1436 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsKleeneAlgebra.starDestructive
d_starDestructive_1438 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_1438 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_starDestructive_2144 (coe v0)
-- Data.Bool.Properties._.IsKleeneAlgebra.starDestructiveʳ
d_starDestructive'691'_1440 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starDestructive'691'_1440 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.starDestructiveˡ
d_starDestructive'737'_1442 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starDestructive'737'_1442 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.starExpansive
d_starExpansive_1444 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_1444 v0
  = coe MAlonzo.Code.Algebra.Structures.d_starExpansive_2142 (coe v0)
-- Data.Bool.Properties._.IsKleeneAlgebra.starExpansiveʳ
d_starExpansive'691'_1446 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starExpansive'691'_1446 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.starExpansiveˡ
d_starExpansive'737'_1448 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starExpansive'737'_1448 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.sym
d_sym_1450 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1450 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.trans
d_trans_1452 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1452 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.zero
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
-- Data.Bool.Properties._.IsKleeneAlgebra.zeroʳ
d_zero'691'_1456 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1456 = erased
-- Data.Bool.Properties._.IsKleeneAlgebra.zeroˡ
d_zero'737'_1458 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1458 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.//-cong
d_'47''47''45'cong_1462 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1462 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.//-congʳ
d_'47''47''45'cong'691'_1464 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1464 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.//-congˡ
d_'47''47''45'cong'737'_1466 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1466 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.\\-cong
d_'92''92''45'cong_1468 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1468 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.\\-congʳ
d_'92''92''45'cong'691'_1470 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1470 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.\\-congˡ
d_'92''92''45'cong'737'_1472 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1472 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.identity
d_identity_1474 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1474 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))
-- Data.Bool.Properties._.IsLeftBolLoop.identityʳ
d_identity'691'_1476 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1476 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.identityˡ
d_identity'737'_1478 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1478 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.isEquivalence
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
-- Data.Bool.Properties._.IsLeftBolLoop.isLoop
d_isLoop_1482 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1482 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)
-- Data.Bool.Properties._.IsLeftBolLoop.isMagma
d_isMagma_1484 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1484 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Bool.Properties._.IsLeftBolLoop.isPartialEquivalence
d_isPartialEquivalence_1486 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsLeftBolLoop.isQuasigroup
d_isQuasigroup_1488 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1488 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))
-- Data.Bool.Properties._.IsLeftBolLoop.leftBol
d_leftBol_1490 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1490 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.leftDivides
d_leftDivides_1492 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1492 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Bool.Properties._.IsLeftBolLoop.leftDividesʳ
d_leftDivides'691'_1494 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1494 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.leftDividesˡ
d_leftDivides'737'_1496 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1496 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.refl
d_refl_1498 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1498 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.reflexive
d_reflexive_1500 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1500 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.rightDivides
d_rightDivides_1502 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1502 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Bool.Properties._.IsLeftBolLoop.rightDividesʳ
d_rightDivides'691'_1504 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1504 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.rightDividesˡ
d_rightDivides'737'_1506 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1506 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.setoid
d_setoid_1508 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsLeftBolLoop.sym
d_sym_1510 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1510 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.trans
d_trans_1512 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1512 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.∙-cong
d_'8729''45'cong_1514 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1514 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.∙-congʳ
d_'8729''45'cong'691'_1516 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1516 = erased
-- Data.Bool.Properties._.IsLeftBolLoop.∙-congˡ
d_'8729''45'cong'737'_1518 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1518 = erased
-- Data.Bool.Properties._.IsLoop.//-cong
d_'47''47''45'cong_1522 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1522 = erased
-- Data.Bool.Properties._.IsLoop.//-congʳ
d_'47''47''45'cong'691'_1524 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1524 = erased
-- Data.Bool.Properties._.IsLoop.//-congˡ
d_'47''47''45'cong'737'_1526 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1526 = erased
-- Data.Bool.Properties._.IsLoop.\\-cong
d_'92''92''45'cong_1528 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1528 = erased
-- Data.Bool.Properties._.IsLoop.\\-congʳ
d_'92''92''45'cong'691'_1530 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1530 = erased
-- Data.Bool.Properties._.IsLoop.\\-congˡ
d_'92''92''45'cong'737'_1532 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1532 = erased
-- Data.Bool.Properties._.IsLoop.identity
d_identity_1534 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1534 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_3138 (coe v0)
-- Data.Bool.Properties._.IsLoop.identityʳ
d_identity'691'_1536 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1536 = erased
-- Data.Bool.Properties._.IsLoop.identityˡ
d_identity'737'_1538 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1538 = erased
-- Data.Bool.Properties._.IsLoop.isEquivalence
d_isEquivalence_1540 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1540 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0)))
-- Data.Bool.Properties._.IsLoop.isMagma
d_isMagma_1542 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Bool.Properties._.IsLoop.isPartialEquivalence
d_isPartialEquivalence_1544 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsLoop.isQuasigroup
d_isQuasigroup_1546 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1546 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0)
-- Data.Bool.Properties._.IsLoop.leftDivides
d_leftDivides_1548 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1548 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Bool.Properties._.IsLoop.leftDividesʳ
d_leftDivides'691'_1550 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1550 = erased
-- Data.Bool.Properties._.IsLoop.leftDividesˡ
d_leftDivides'737'_1552 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1552 = erased
-- Data.Bool.Properties._.IsLoop.refl
d_refl_1554 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1554 = erased
-- Data.Bool.Properties._.IsLoop.reflexive
d_reflexive_1556 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1556 = erased
-- Data.Bool.Properties._.IsLoop.rightDivides
d_rightDivides_1558 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1558 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Bool.Properties._.IsLoop.rightDividesʳ
d_rightDivides'691'_1560 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1560 = erased
-- Data.Bool.Properties._.IsLoop.rightDividesˡ
d_rightDivides'737'_1562 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1562 = erased
-- Data.Bool.Properties._.IsLoop.setoid
d_setoid_1564 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsLoop.sym
d_sym_1566 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1566 = erased
-- Data.Bool.Properties._.IsLoop.trans
d_trans_1568 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1568 = erased
-- Data.Bool.Properties._.IsLoop.∙-cong
d_'8729''45'cong_1570 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1570 = erased
-- Data.Bool.Properties._.IsLoop.∙-congʳ
d_'8729''45'cong'691'_1572 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1572 = erased
-- Data.Bool.Properties._.IsLoop.∙-congˡ
d_'8729''45'cong'737'_1574 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1574 = erased
-- Data.Bool.Properties._.IsMagma.isEquivalence
d_isEquivalence_1578 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1578 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0)
-- Data.Bool.Properties._.IsMagma.isPartialEquivalence
d_isPartialEquivalence_1580 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsMagma.refl
d_refl_1582 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1582 = erased
-- Data.Bool.Properties._.IsMagma.reflexive
d_reflexive_1584 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1584 = erased
-- Data.Bool.Properties._.IsMagma.setoid
d_setoid_1586 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1586 v0 v1
  = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 v1
-- Data.Bool.Properties._.IsMagma.sym
d_sym_1588 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1588 = erased
-- Data.Bool.Properties._.IsMagma.trans
d_trans_1590 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1590 = erased
-- Data.Bool.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1592 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1592 = erased
-- Data.Bool.Properties._.IsMagma.∙-congʳ
d_'8729''45'cong'691'_1594 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1594 = erased
-- Data.Bool.Properties._.IsMagma.∙-congˡ
d_'8729''45'cong'737'_1596 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1596 = erased
-- Data.Bool.Properties._.IsMedialMagma.isEquivalence
d_isEquivalence_1600 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1600 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0))
-- Data.Bool.Properties._.IsMedialMagma.isMagma
d_isMagma_1602 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1602 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0)
-- Data.Bool.Properties._.IsMedialMagma.isPartialEquivalence
d_isPartialEquivalence_1604 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsMedialMagma.medial
d_medial_1606 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Bool ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_medial_1606 = erased
-- Data.Bool.Properties._.IsMedialMagma.refl
d_refl_1608 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1608 = erased
-- Data.Bool.Properties._.IsMedialMagma.reflexive
d_reflexive_1610 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1610 = erased
-- Data.Bool.Properties._.IsMedialMagma.setoid
d_setoid_1612 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsMedialMagma.sym
d_sym_1614 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1614 = erased
-- Data.Bool.Properties._.IsMedialMagma.trans
d_trans_1616 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1616 = erased
-- Data.Bool.Properties._.IsMedialMagma.∙-cong
d_'8729''45'cong_1618 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1618 = erased
-- Data.Bool.Properties._.IsMedialMagma.∙-congʳ
d_'8729''45'cong'691'_1620 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1620 = erased
-- Data.Bool.Properties._.IsMedialMagma.∙-congˡ
d_'8729''45'cong'737'_1622 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1622 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.//-cong
d_'47''47''45'cong_1626 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1626 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.//-congʳ
d_'47''47''45'cong'691'_1628 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1628 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.//-congˡ
d_'47''47''45'cong'737'_1630 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1630 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.\\-cong
d_'92''92''45'cong_1632 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1632 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.\\-congʳ
d_'92''92''45'cong'691'_1634 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1634 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.\\-congˡ
d_'92''92''45'cong'737'_1636 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1636 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.identity
d_identity_1638 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1638 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))
-- Data.Bool.Properties._.IsMiddleBolLoop.identityʳ
d_identity'691'_1640 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1640 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.identityˡ
d_identity'737'_1642 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1642 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.isEquivalence
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
-- Data.Bool.Properties._.IsMiddleBolLoop.isLoop
d_isLoop_1646 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1646 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)
-- Data.Bool.Properties._.IsMiddleBolLoop.isMagma
d_isMagma_1648 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1648 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Bool.Properties._.IsMiddleBolLoop.isPartialEquivalence
d_isPartialEquivalence_1650 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsMiddleBolLoop.isQuasigroup
d_isQuasigroup_1652 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1652 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))
-- Data.Bool.Properties._.IsMiddleBolLoop.leftDivides
d_leftDivides_1654 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1654 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Bool.Properties._.IsMiddleBolLoop.leftDividesʳ
d_leftDivides'691'_1656 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1656 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.leftDividesˡ
d_leftDivides'737'_1658 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1658 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.middleBol
d_middleBol_1660 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_middleBol_1660 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.refl
d_refl_1662 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1662 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.reflexive
d_reflexive_1664 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1664 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.rightDivides
d_rightDivides_1666 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1666 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Bool.Properties._.IsMiddleBolLoop.rightDividesʳ
d_rightDivides'691'_1668 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1668 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.rightDividesˡ
d_rightDivides'737'_1670 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1670 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.setoid
d_setoid_1672 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsMiddleBolLoop.sym
d_sym_1674 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1674 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.trans
d_trans_1676 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1676 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.∙-cong
d_'8729''45'cong_1678 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1678 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.∙-congʳ
d_'8729''45'cong'691'_1680 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1680 = erased
-- Data.Bool.Properties._.IsMiddleBolLoop.∙-congˡ
d_'8729''45'cong'737'_1682 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1682 = erased
-- Data.Bool.Properties._.IsMonoid.assoc
d_assoc_1686 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1686 = erased
-- Data.Bool.Properties._.IsMonoid.identity
d_identity_1688 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1688 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_724 (coe v0)
-- Data.Bool.Properties._.IsMonoid.identityʳ
d_identity'691'_1690 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1690 = erased
-- Data.Bool.Properties._.IsMonoid.identityˡ
d_identity'737'_1692 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1692 = erased
-- Data.Bool.Properties._.IsMonoid.isEquivalence
d_isEquivalence_1694 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1694 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)))
-- Data.Bool.Properties._.IsMonoid.isMagma
d_isMagma_1696 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1696 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0))
-- Data.Bool.Properties._.IsMonoid.isPartialEquivalence
d_isPartialEquivalence_1698 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1700 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1700 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)
-- Data.Bool.Properties._.IsMonoid.isUnitalMagma
d_isUnitalMagma_1702 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1702 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756 v2
-- Data.Bool.Properties._.IsMonoid.refl
d_refl_1704 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1704 = erased
-- Data.Bool.Properties._.IsMonoid.reflexive
d_reflexive_1706 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1706 = erased
-- Data.Bool.Properties._.IsMonoid.setoid
d_setoid_1708 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsMonoid.sym
d_sym_1710 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1710 = erased
-- Data.Bool.Properties._.IsMonoid.trans
d_trans_1712 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1712 = erased
-- Data.Bool.Properties._.IsMonoid.∙-cong
d_'8729''45'cong_1714 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1714 = erased
-- Data.Bool.Properties._.IsMonoid.∙-congʳ
d_'8729''45'cong'691'_1716 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1716 = erased
-- Data.Bool.Properties._.IsMonoid.∙-congˡ
d_'8729''45'cong'737'_1718 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1718 = erased
-- Data.Bool.Properties._.IsMoufangLoop.//-cong
d_'47''47''45'cong_1722 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1722 = erased
-- Data.Bool.Properties._.IsMoufangLoop.//-congʳ
d_'47''47''45'cong'691'_1724 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1724 = erased
-- Data.Bool.Properties._.IsMoufangLoop.//-congˡ
d_'47''47''45'cong'737'_1726 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1726 = erased
-- Data.Bool.Properties._.IsMoufangLoop.\\-cong
d_'92''92''45'cong_1728 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1728 = erased
-- Data.Bool.Properties._.IsMoufangLoop.\\-congʳ
d_'92''92''45'cong'691'_1730 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1730 = erased
-- Data.Bool.Properties._.IsMoufangLoop.\\-congˡ
d_'92''92''45'cong'737'_1732 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1732 = erased
-- Data.Bool.Properties._.IsMoufangLoop.identical
d_identical_1734 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identical_1734 = erased
-- Data.Bool.Properties._.IsMoufangLoop.identity
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
-- Data.Bool.Properties._.IsMoufangLoop.identityʳ
d_identity'691'_1738 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1738 = erased
-- Data.Bool.Properties._.IsMoufangLoop.identityˡ
d_identity'737'_1740 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1740 = erased
-- Data.Bool.Properties._.IsMoufangLoop.isEquivalence
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
-- Data.Bool.Properties._.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_1744 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202
d_isLeftBolLoop_1744 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)
-- Data.Bool.Properties._.IsMoufangLoop.isLoop
d_isLoop_1746 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1746 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isLoop_3216
      (coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))
-- Data.Bool.Properties._.IsMoufangLoop.isMagma
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
-- Data.Bool.Properties._.IsMoufangLoop.isPartialEquivalence
d_isPartialEquivalence_1750 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsMoufangLoop.isQuasigroup
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
-- Data.Bool.Properties._.IsMoufangLoop.leftBol
d_leftBol_1754 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1754 = erased
-- Data.Bool.Properties._.IsMoufangLoop.leftDivides
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
-- Data.Bool.Properties._.IsMoufangLoop.leftDividesʳ
d_leftDivides'691'_1758 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1758 = erased
-- Data.Bool.Properties._.IsMoufangLoop.leftDividesˡ
d_leftDivides'737'_1760 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1760 = erased
-- Data.Bool.Properties._.IsMoufangLoop.refl
d_refl_1762 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1762 = erased
-- Data.Bool.Properties._.IsMoufangLoop.reflexive
d_reflexive_1764 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1764 = erased
-- Data.Bool.Properties._.IsMoufangLoop.rightBol
d_rightBol_1766 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_1766 = erased
-- Data.Bool.Properties._.IsMoufangLoop.rightDivides
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
-- Data.Bool.Properties._.IsMoufangLoop.rightDividesʳ
d_rightDivides'691'_1770 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1770 = erased
-- Data.Bool.Properties._.IsMoufangLoop.rightDividesˡ
d_rightDivides'737'_1772 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1772 = erased
-- Data.Bool.Properties._.IsMoufangLoop.setoid
d_setoid_1774 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsMoufangLoop.sym
d_sym_1776 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1776 = erased
-- Data.Bool.Properties._.IsMoufangLoop.trans
d_trans_1778 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1778 = erased
-- Data.Bool.Properties._.IsMoufangLoop.∙-cong
d_'8729''45'cong_1780 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1780 = erased
-- Data.Bool.Properties._.IsMoufangLoop.∙-congʳ
d_'8729''45'cong'691'_1782 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1782 = erased
-- Data.Bool.Properties._.IsMoufangLoop.∙-congˡ
d_'8729''45'cong'737'_1784 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1784 = erased
-- Data.Bool.Properties._.IsNearSemiring.*-assoc
d_'42''45'assoc_1788 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1788 = erased
-- Data.Bool.Properties._.IsNearSemiring.*-cong
d_'42''45'cong_1790 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1790 = erased
-- Data.Bool.Properties._.IsNearSemiring.∙-congʳ
d_'8729''45'cong'691'_1792 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1792 = erased
-- Data.Bool.Properties._.IsNearSemiring.∙-congˡ
d_'8729''45'cong'737'_1794 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1794 = erased
-- Data.Bool.Properties._.IsNearSemiring.*-isMagma
d_'42''45'isMagma_1796 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1796 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324 v3
-- Data.Bool.Properties._.IsNearSemiring.*-isSemigroup
d_'42''45'isSemigroup_1798 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1798 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326 v3
-- Data.Bool.Properties._.IsNearSemiring.assoc
d_assoc_1800 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1800 = erased
-- Data.Bool.Properties._.IsNearSemiring.∙-cong
d_'8729''45'cong_1802 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1802 = erased
-- Data.Bool.Properties._.IsNearSemiring.∙-congʳ
d_'8729''45'cong'691'_1804 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1804 = erased
-- Data.Bool.Properties._.IsNearSemiring.∙-congˡ
d_'8729''45'cong'737'_1806 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1806 = erased
-- Data.Bool.Properties._.IsNearSemiring.identity
d_identity_1808 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1808 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Bool.Properties._.IsNearSemiring.identityʳ
d_identity'691'_1810 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1810 = erased
-- Data.Bool.Properties._.IsNearSemiring.identityˡ
d_identity'737'_1812 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1812 = erased
-- Data.Bool.Properties._.IsNearSemiring.isMagma
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
-- Data.Bool.Properties._.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1816 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1816 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0)
-- Data.Bool.Properties._.IsNearSemiring.isSemigroup
d_isSemigroup_1818 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1818 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Bool.Properties._.IsNearSemiring.isUnitalMagma
d_isUnitalMagma_1820 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsNearSemiring.distribʳ
d_distrib'691'_1822 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1822 = erased
-- Data.Bool.Properties._.IsNearSemiring.isEquivalence
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
-- Data.Bool.Properties._.IsNearSemiring.isPartialEquivalence
d_isPartialEquivalence_1826 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsNearSemiring.refl
d_refl_1828 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1828 = erased
-- Data.Bool.Properties._.IsNearSemiring.reflexive
d_reflexive_1830 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1830 = erased
-- Data.Bool.Properties._.IsNearSemiring.setoid
d_setoid_1832 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsNearSemiring.sym
d_sym_1834 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1834 = erased
-- Data.Bool.Properties._.IsNearSemiring.trans
d_trans_1836 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1836 = erased
-- Data.Bool.Properties._.IsNearSemiring.zeroˡ
d_zero'737'_1838 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1838 = erased
-- Data.Bool.Properties._.IsNearring.*-assoc
d_'42''45'assoc_1842 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1842 = erased
-- Data.Bool.Properties._.IsNearring.*-cong
d_'42''45'cong_1844 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1844 = erased
-- Data.Bool.Properties._.IsNearring.∙-congʳ
d_'8729''45'cong'691'_1846 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1846 = erased
-- Data.Bool.Properties._.IsNearring.∙-congˡ
d_'8729''45'cong'737'_1848 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1848 = erased
-- Data.Bool.Properties._.IsNearring.*-identity
d_'42''45'identity_1850 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1850 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2288
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Bool.Properties._.IsNearring.identityʳ
d_identity'691'_1852 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1852 = erased
-- Data.Bool.Properties._.IsNearring.identityˡ
d_identity'737'_1854 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1854 = erased
-- Data.Bool.Properties._.IsNearring.*-isMagma
d_'42''45'isMagma_1856 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsNearring.*-isMonoid
d_'42''45'isMonoid_1858 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsNearring.*-isSemigroup
d_'42''45'isSemigroup_1860 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsNearring.assoc
d_assoc_1862 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1862 = erased
-- Data.Bool.Properties._.IsNearring.∙-cong
d_'8729''45'cong_1864 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1864 = erased
-- Data.Bool.Properties._.IsNearring.∙-congʳ
d_'8729''45'cong'691'_1866 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1866 = erased
-- Data.Bool.Properties._.IsNearring.∙-congˡ
d_'8729''45'cong'737'_1868 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1868 = erased
-- Data.Bool.Properties._.IsNearring.identity
d_identity_1870 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1870 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))
-- Data.Bool.Properties._.IsNearring.identityʳ
d_identity'691'_1872 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1872 = erased
-- Data.Bool.Properties._.IsNearring.identityˡ
d_identity'737'_1874 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1874 = erased
-- Data.Bool.Properties._.IsNearring.+-inverse
d_'43''45'inverse_1876 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_1876 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'inverse_2646 (coe v0)
-- Data.Bool.Properties._.IsNearring.+-inverseʳ
d_'43''45'inverse'691'_1878 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'691'_1878 = erased
-- Data.Bool.Properties._.IsNearring.+-inverseˡ
d_'43''45'inverse'737'_1880 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'737'_1880 = erased
-- Data.Bool.Properties._.IsNearring.isMagma
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
-- Data.Bool.Properties._.IsNearring.+-isMonoid
d_'43''45'isMonoid_1884 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1884 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Bool.Properties._.IsNearring.isSemigroup
d_isSemigroup_1886 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1886 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))
-- Data.Bool.Properties._.IsNearring.isUnitalMagma
d_isUnitalMagma_1888 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsNearring.distrib
d_distrib_1890 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1890 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2290
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Bool.Properties._.IsNearring.distribʳ
d_distrib'691'_1892 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1892 = erased
-- Data.Bool.Properties._.IsNearring.distribˡ
d_distrib'737'_1894 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1894 = erased
-- Data.Bool.Properties._.IsNearring.identityʳ
d_identity'691'_1896 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1896 = erased
-- Data.Bool.Properties._.IsNearring.identityˡ
d_identity'737'_1898 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1898 = erased
-- Data.Bool.Properties._.IsNearring.isEquivalence
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
-- Data.Bool.Properties._.IsNearring.isPartialEquivalence
d_isPartialEquivalence_1902 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsNearring.isQuasiring
d_isQuasiring_1904 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260
d_isQuasiring_1904 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)
-- Data.Bool.Properties._.IsNearring.refl
d_refl_1906 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1906 = erased
-- Data.Bool.Properties._.IsNearring.reflexive
d_reflexive_1908 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1908 = erased
-- Data.Bool.Properties._.IsNearring.setoid
d_setoid_1910 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsNearring.sym
d_sym_1912 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1912 = erased
-- Data.Bool.Properties._.IsNearring.trans
d_trans_1914 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1914 = erased
-- Data.Bool.Properties._.IsNearring.zero
d_zero_1916 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1916 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_2292
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Bool.Properties._.IsNearring.zeroʳ
d_zero'691'_1918 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1918 = erased
-- Data.Bool.Properties._.IsNearring.zeroˡ
d_zero'737'_1920 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  (Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1920 = erased
-- Data.Bool.Properties._.IsNearring.⁻¹-cong
d_'8315''185''45'cong_1922 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1922 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing._//_
d__'47''47'__1926 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> Bool -> Bool
d__'47''47'__1926 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__1926 v0 v2
du__'47''47'__1926 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool -> Bool
du__'47''47'__1926 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Bool.Properties._.IsNonAssociativeRing.*-cong
d_'42''45'cong_1928 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1928 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.∙-congʳ
d_'8729''45'cong'691'_1930 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1930 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.∙-congˡ
d_'8729''45'cong'737'_1932 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1932 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.*-identity
d_'42''45'identity_1934 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1934 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2520 (coe v0)
-- Data.Bool.Properties._.IsNonAssociativeRing.*-identityʳ
d_'42''45'identity'691'_1936 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_1936 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.*-identityˡ
d_'42''45'identity'737'_1938 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_1938 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.*-isMagma
d_'42''45'isMagma_1940 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1940 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2600 v5
-- Data.Bool.Properties._.IsNonAssociativeRing.*-isUnitalMagma
d_'42''45'isUnitalMagma_1942 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_'42''45'isUnitalMagma_1942 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isUnitalMagma_2606 v5
-- Data.Bool.Properties._.IsNonAssociativeRing.assoc
d_assoc_1944 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1944 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.comm
d_comm_1946 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1946 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.∙-cong
d_'8729''45'cong_1948 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1948 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.∙-congʳ
d_'8729''45'cong'691'_1950 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1950 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.∙-congˡ
d_'8729''45'cong'737'_1952 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1952 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.identity
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
-- Data.Bool.Properties._.IsNonAssociativeRing.identityʳ
d_identity'691'_1956 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1956 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.identityˡ
d_identity'737'_1958 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1958 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_1960 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_1960 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
      (coe v0)
-- Data.Bool.Properties._.IsNonAssociativeRing.isCommutativeMagma
d_isCommutativeMagma_1962 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isCommutativeMonoid
d_isCommutativeMonoid_1964 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_1966 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isGroup
d_isGroup_1968 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_1968 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
         (coe v0))
-- Data.Bool.Properties._.IsNonAssociativeRing.isInvertibleMagma
d_isInvertibleMagma_1970 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1972 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isMagma
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isMonoid
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isSemigroup
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isUnitalMagma
d_isUnitalMagma_1980 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsNonAssociativeRing.⁻¹-cong
d_'8315''185''45'cong_1982 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1982 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.inverse
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
-- Data.Bool.Properties._.IsNonAssociativeRing.inverseʳ
d_inverse'691'_1986 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1986 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.inverseˡ
d_inverse'737'_1988 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1988 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.distrib
d_distrib_1990 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1990 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2522 (coe v0)
-- Data.Bool.Properties._.IsNonAssociativeRing.distribʳ
d_distrib'691'_1992 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1992 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.distribˡ
d_distrib'737'_1994 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1994 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.isEquivalence
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
-- Data.Bool.Properties._.IsNonAssociativeRing.isPartialEquivalence
d_isPartialEquivalence_1998 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsNonAssociativeRing.refl
d_refl_2000 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2000 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.reflexive
d_reflexive_2002 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2002 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.setoid
d_setoid_2004 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsNonAssociativeRing.sym
d_sym_2006 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2006 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.trans
d_trans_2008 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2008 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2010 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2010 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2012 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2012 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.zero
d_zero_2014 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2014 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2524 (coe v0)
-- Data.Bool.Properties._.IsNonAssociativeRing.zeroʳ
d_zero'691'_2016 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2016 = erased
-- Data.Bool.Properties._.IsNonAssociativeRing.zeroˡ
d_zero'737'_2018 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2018 = erased
-- Data.Bool.Properties._.IsQuasigroup.//-cong
d_'47''47''45'cong_2022 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2022 = erased
-- Data.Bool.Properties._.IsQuasigroup.//-congʳ
d_'47''47''45'cong'691'_2024 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_2024 = erased
-- Data.Bool.Properties._.IsQuasigroup.//-congˡ
d_'47''47''45'cong'737'_2026 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_2026 = erased
-- Data.Bool.Properties._.IsQuasigroup.\\-cong
d_'92''92''45'cong_2028 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2028 = erased
-- Data.Bool.Properties._.IsQuasigroup.\\-congʳ
d_'92''92''45'cong'691'_2030 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_2030 = erased
-- Data.Bool.Properties._.IsQuasigroup.\\-congˡ
d_'92''92''45'cong'737'_2032 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_2032 = erased
-- Data.Bool.Properties._.IsQuasigroup.isEquivalence
d_isEquivalence_2034 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2034 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0))
-- Data.Bool.Properties._.IsQuasigroup.isMagma
d_isMagma_2036 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2036 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0)
-- Data.Bool.Properties._.IsQuasigroup.isPartialEquivalence
d_isPartialEquivalence_2038 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsQuasigroup.leftDivides
d_leftDivides_2040 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2040 v0
  = coe MAlonzo.Code.Algebra.Structures.d_leftDivides_3062 (coe v0)
-- Data.Bool.Properties._.IsQuasigroup.leftDividesʳ
d_leftDivides'691'_2042 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_2042 = erased
-- Data.Bool.Properties._.IsQuasigroup.leftDividesˡ
d_leftDivides'737'_2044 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_2044 = erased
-- Data.Bool.Properties._.IsQuasigroup.refl
d_refl_2046 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2046 = erased
-- Data.Bool.Properties._.IsQuasigroup.reflexive
d_reflexive_2048 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2048 = erased
-- Data.Bool.Properties._.IsQuasigroup.rightDivides
d_rightDivides_2050 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2050 v0
  = coe MAlonzo.Code.Algebra.Structures.d_rightDivides_3064 (coe v0)
-- Data.Bool.Properties._.IsQuasigroup.rightDividesʳ
d_rightDivides'691'_2052 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_2052 = erased
-- Data.Bool.Properties._.IsQuasigroup.rightDividesˡ
d_rightDivides'737'_2054 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_2054 = erased
-- Data.Bool.Properties._.IsQuasigroup.setoid
d_setoid_2056 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsQuasigroup.sym
d_sym_2058 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2058 = erased
-- Data.Bool.Properties._.IsQuasigroup.trans
d_trans_2060 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2060 = erased
-- Data.Bool.Properties._.IsQuasigroup.∙-cong
d_'8729''45'cong_2062 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2062 = erased
-- Data.Bool.Properties._.IsQuasigroup.∙-congʳ
d_'8729''45'cong'691'_2064 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2064 = erased
-- Data.Bool.Properties._.IsQuasigroup.∙-congˡ
d_'8729''45'cong'737'_2066 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2066 = erased
-- Data.Bool.Properties._.IsQuasiring.*-assoc
d_'42''45'assoc_2070 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2070 = erased
-- Data.Bool.Properties._.IsQuasiring.*-cong
d_'42''45'cong_2072 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2072 = erased
-- Data.Bool.Properties._.IsQuasiring.∙-congʳ
d_'8729''45'cong'691'_2074 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2074 = erased
-- Data.Bool.Properties._.IsQuasiring.∙-congˡ
d_'8729''45'cong'737'_2076 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2076 = erased
-- Data.Bool.Properties._.IsQuasiring.*-identity
d_'42''45'identity_2078 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2078 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2288 (coe v0)
-- Data.Bool.Properties._.IsQuasiring.identityʳ
d_identity'691'_2080 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2080 = erased
-- Data.Bool.Properties._.IsQuasiring.identityˡ
d_identity'737'_2082 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2082 = erased
-- Data.Bool.Properties._.IsQuasiring.*-isMagma
d_'42''45'isMagma_2084 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2084 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2342 v4
-- Data.Bool.Properties._.IsQuasiring.*-isMonoid
d_'42''45'isMonoid_2086 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2086 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2346 v4
-- Data.Bool.Properties._.IsQuasiring.*-isSemigroup
d_'42''45'isSemigroup_2088 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2088 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_2344 v4
-- Data.Bool.Properties._.IsQuasiring.assoc
d_assoc_2090 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2090 = erased
-- Data.Bool.Properties._.IsQuasiring.∙-cong
d_'8729''45'cong_2092 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2092 = erased
-- Data.Bool.Properties._.IsQuasiring.∙-congʳ
d_'8729''45'cong'691'_2094 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2094 = erased
-- Data.Bool.Properties._.IsQuasiring.∙-congˡ
d_'8729''45'cong'737'_2096 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2096 = erased
-- Data.Bool.Properties._.IsQuasiring.identity
d_identity_2098 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2098 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Bool.Properties._.IsQuasiring.identityʳ
d_identity'691'_2100 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2100 = erased
-- Data.Bool.Properties._.IsQuasiring.identityˡ
d_identity'737'_2102 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2102 = erased
-- Data.Bool.Properties._.IsQuasiring.isMagma
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
-- Data.Bool.Properties._.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_2106 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_2106 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0)
-- Data.Bool.Properties._.IsQuasiring.isSemigroup
d_isSemigroup_2108 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2108 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Bool.Properties._.IsQuasiring.isUnitalMagma
d_isUnitalMagma_2110 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsQuasiring.distrib
d_distrib_2112 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2112 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2290 (coe v0)
-- Data.Bool.Properties._.IsQuasiring.distribʳ
d_distrib'691'_2114 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2114 = erased
-- Data.Bool.Properties._.IsQuasiring.distribˡ
d_distrib'737'_2116 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2116 = erased
-- Data.Bool.Properties._.IsQuasiring.identityʳ
d_identity'691'_2118 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2118 = erased
-- Data.Bool.Properties._.IsQuasiring.identityˡ
d_identity'737'_2120 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2120 = erased
-- Data.Bool.Properties._.IsQuasiring.isEquivalence
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
-- Data.Bool.Properties._.IsQuasiring.isPartialEquivalence
d_isPartialEquivalence_2124 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsQuasiring.refl
d_refl_2126 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2126 = erased
-- Data.Bool.Properties._.IsQuasiring.reflexive
d_reflexive_2128 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2128 = erased
-- Data.Bool.Properties._.IsQuasiring.setoid
d_setoid_2130 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsQuasiring.sym
d_sym_2132 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2132 = erased
-- Data.Bool.Properties._.IsQuasiring.trans
d_trans_2134 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2134 = erased
-- Data.Bool.Properties._.IsQuasiring.zero
d_zero_2136 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2136 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2292 (coe v0)
-- Data.Bool.Properties._.IsQuasiring.zeroʳ
d_zero'691'_2138 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2138 = erased
-- Data.Bool.Properties._.IsQuasiring.zeroˡ
d_zero'737'_2140 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2140 = erased
-- Data.Bool.Properties._.IsRightBolLoop.//-cong
d_'47''47''45'cong_2144 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2144 = erased
-- Data.Bool.Properties._.IsRightBolLoop.//-congʳ
d_'47''47''45'cong'691'_2146 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_2146 = erased
-- Data.Bool.Properties._.IsRightBolLoop.//-congˡ
d_'47''47''45'cong'737'_2148 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_2148 = erased
-- Data.Bool.Properties._.IsRightBolLoop.\\-cong
d_'92''92''45'cong_2150 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2150 = erased
-- Data.Bool.Properties._.IsRightBolLoop.\\-congʳ
d_'92''92''45'cong'691'_2152 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_2152 = erased
-- Data.Bool.Properties._.IsRightBolLoop.\\-congˡ
d_'92''92''45'cong'737'_2154 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_2154 = erased
-- Data.Bool.Properties._.IsRightBolLoop.identity
d_identity_2156 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2156 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))
-- Data.Bool.Properties._.IsRightBolLoop.identityʳ
d_identity'691'_2158 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2158 = erased
-- Data.Bool.Properties._.IsRightBolLoop.identityˡ
d_identity'737'_2160 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2160 = erased
-- Data.Bool.Properties._.IsRightBolLoop.isEquivalence
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
-- Data.Bool.Properties._.IsRightBolLoop.isLoop
d_isLoop_2164 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_2164 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)
-- Data.Bool.Properties._.IsRightBolLoop.isMagma
d_isMagma_2166 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2166 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Bool.Properties._.IsRightBolLoop.isPartialEquivalence
d_isPartialEquivalence_2168 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRightBolLoop.isQuasigroup
d_isQuasigroup_2170 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_2170 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))
-- Data.Bool.Properties._.IsRightBolLoop.leftDivides
d_leftDivides_2172 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2172 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Bool.Properties._.IsRightBolLoop.leftDividesʳ
d_leftDivides'691'_2174 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_2174 = erased
-- Data.Bool.Properties._.IsRightBolLoop.leftDividesˡ
d_leftDivides'737'_2176 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_2176 = erased
-- Data.Bool.Properties._.IsRightBolLoop.refl
d_refl_2178 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2178 = erased
-- Data.Bool.Properties._.IsRightBolLoop.reflexive
d_reflexive_2180 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2180 = erased
-- Data.Bool.Properties._.IsRightBolLoop.rightBol
d_rightBol_2182 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_2182 = erased
-- Data.Bool.Properties._.IsRightBolLoop.rightDivides
d_rightDivides_2184 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2184 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Bool.Properties._.IsRightBolLoop.rightDividesʳ
d_rightDivides'691'_2186 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_2186 = erased
-- Data.Bool.Properties._.IsRightBolLoop.rightDividesˡ
d_rightDivides'737'_2188 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_2188 = erased
-- Data.Bool.Properties._.IsRightBolLoop.setoid
d_setoid_2190 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRightBolLoop.sym
d_sym_2192 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2192 = erased
-- Data.Bool.Properties._.IsRightBolLoop.trans
d_trans_2194 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2194 = erased
-- Data.Bool.Properties._.IsRightBolLoop.∙-cong
d_'8729''45'cong_2196 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2196 = erased
-- Data.Bool.Properties._.IsRightBolLoop.∙-congʳ
d_'8729''45'cong'691'_2198 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2198 = erased
-- Data.Bool.Properties._.IsRightBolLoop.∙-congˡ
d_'8729''45'cong'737'_2200 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2200 = erased
-- Data.Bool.Properties._.IsRing._//_
d__'47''47'__2204 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> Bool -> Bool
d__'47''47'__2204 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__2204 v0 v2
du__'47''47'__2204 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool -> Bool
du__'47''47'__2204 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Bool.Properties._.IsRing.*-assoc
d_'42''45'assoc_2206 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2206 = erased
-- Data.Bool.Properties._.IsRing.*-cong
d_'42''45'cong_2208 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2208 = erased
-- Data.Bool.Properties._.IsRing.∙-congʳ
d_'8729''45'cong'691'_2210 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2210 = erased
-- Data.Bool.Properties._.IsRing.∙-congˡ
d_'8729''45'cong'737'_2212 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2212 = erased
-- Data.Bool.Properties._.IsRing.*-identity
d_'42''45'identity_2214 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2214 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768 (coe v0)
-- Data.Bool.Properties._.IsRing.identityʳ
d_identity'691'_2216 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2216 = erased
-- Data.Bool.Properties._.IsRing.identityˡ
d_identity'737'_2218 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2218 = erased
-- Data.Bool.Properties._.IsRing.*-isMagma
d_'42''45'isMagma_2220 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2220 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMagma_2220 v0 v1 v2 v3 v5
du_'42''45'isMagma_2220 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.*-isMonoid
d_'42''45'isMonoid_2222 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2222 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2860 v0 v1 v2
      v3 v5
-- Data.Bool.Properties._.IsRing.*-isSemigroup
d_'42''45'isSemigroup_2224 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2224 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isSemigroup_2224 v0 v1 v2 v3 v5
du_'42''45'isSemigroup_2224 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.assoc
d_assoc_2226 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2226 = erased
-- Data.Bool.Properties._.IsRing.comm
d_comm_2228 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2228 = erased
-- Data.Bool.Properties._.IsRing.∙-cong
d_'8729''45'cong_2230 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2230 = erased
-- Data.Bool.Properties._.IsRing.∙-congʳ
d_'8729''45'cong'691'_2232 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2232 = erased
-- Data.Bool.Properties._.IsRing.∙-congˡ
d_'8729''45'cong'737'_2234 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2234 = erased
-- Data.Bool.Properties._.IsRing.identity
d_identity_2236 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.identityʳ
d_identity'691'_2238 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2238 = erased
-- Data.Bool.Properties._.IsRing.identityˡ
d_identity'737'_2240 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2240 = erased
-- Data.Bool.Properties._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2242 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2242 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe v0)
-- Data.Bool.Properties._.IsRing.isCommutativeMagma
d_isCommutativeMagma_2244 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isCommutativeMonoid
d_isCommutativeMonoid_2246 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isCommutativeSemigroup
d_isCommutativeSemigroup_2248 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isGroup
d_isGroup_2250 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isInvertibleMagma
d_isInvertibleMagma_2252 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2254 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isMagma
d_isMagma_2256 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isMonoid
d_isMonoid_2258 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isSemigroup
d_isSemigroup_2260 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isUnitalMagma
d_isUnitalMagma_2262 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.⁻¹-cong
d_'8315''185''45'cong_2264 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2264 = erased
-- Data.Bool.Properties._.IsRing.inverse
d_inverse_2266 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.inverseʳ
d_inverse'691'_2268 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_2268 = erased
-- Data.Bool.Properties._.IsRing.inverseˡ
d_inverse'737'_2270 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_2270 = erased
-- Data.Bool.Properties._.IsRing.distrib
d_distrib_2272 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2272 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2770 (coe v0)
-- Data.Bool.Properties._.IsRing.distribʳ
d_distrib'691'_2274 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2274 = erased
-- Data.Bool.Properties._.IsRing.distribˡ
d_distrib'737'_2276 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2276 = erased
-- Data.Bool.Properties._.IsRing.isEquivalence
d_isEquivalence_2278 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isNearSemiring
d_isNearSemiring_2280 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2280 v0 v1 v2 v3 ~v4 v5
  = du_isNearSemiring_2280 v0 v1 v2 v3 v5
du_isNearSemiring_2280 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_2280 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v4))
-- Data.Bool.Properties._.IsRing.isPartialEquivalence
d_isPartialEquivalence_2282 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.isRingWithoutOne
d_isRingWithoutOne_2284 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
d_isRingWithoutOne_2284 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 v5
-- Data.Bool.Properties._.IsRing.isSemiring
d_isSemiring_2286 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_2286 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 v0 v1 v2 v3 v5
-- Data.Bool.Properties._.IsRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2288 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2288 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2868
      v5
-- Data.Bool.Properties._.IsRing.isSemiringWithoutOne
d_isSemiringWithoutOne_2290 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2290 v0 v1 v2 v3 ~v4 v5
  = du_isSemiringWithoutOne_2290 v0 v1 v2 v3 v5
du_isSemiringWithoutOne_2290 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2290 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Bool.Properties._.IsRing.refl
d_refl_2292 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2292 = erased
-- Data.Bool.Properties._.IsRing.reflexive
d_reflexive_2294 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2294 = erased
-- Data.Bool.Properties._.IsRing.setoid
d_setoid_2296 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsRing.sym
d_sym_2298 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2298 = erased
-- Data.Bool.Properties._.IsRing.trans
d_trans_2300 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2300 = erased
-- Data.Bool.Properties._.IsRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2302 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2302 = erased
-- Data.Bool.Properties._.IsRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2304 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2304 = erased
-- Data.Bool.Properties._.IsRing.zero
d_zero_2306 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2306 v0 v1 v2 v3 ~v4 v5 = du_zero_2306 v0 v1 v2 v3 v5
du_zero_2306 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2306 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_zero_2468 (coe v0) (coe v1)
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v4))
-- Data.Bool.Properties._.IsRing.zeroʳ
d_zero'691'_2308 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2308 = erased
-- Data.Bool.Properties._.IsRing.zeroˡ
d_zero'737'_2310 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2310 = erased
-- Data.Bool.Properties._.IsRingWithoutOne._//_
d__'47''47'__2314 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> Bool -> Bool
d__'47''47'__2314 v0 ~v1 v2 ~v3 ~v4 = du__'47''47'__2314 v0 v2
du__'47''47'__2314 ::
  (Bool -> Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool -> Bool
du__'47''47'__2314 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Bool.Properties._.IsRingWithoutOne.*-assoc
d_'42''45'assoc_2316 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2316 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.*-cong
d_'42''45'cong_2318 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2318 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2320 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2320 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2322 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2322 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.*-isMagma
d_'42''45'isMagma_2324 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2324 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Bool.Properties._.IsRingWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2326 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2326 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Bool.Properties._.IsRingWithoutOne.assoc
d_assoc_2328 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2328 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.comm
d_comm_2330 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2330 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.∙-cong
d_'8729''45'cong_2332 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2332 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2334 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2334 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2336 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2336 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.identity
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
-- Data.Bool.Properties._.IsRingWithoutOne.identityʳ
d_identity'691'_2340 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2340 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.identityˡ
d_identity'737'_2342 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2342 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2344 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2344 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
      (coe v0)
-- Data.Bool.Properties._.IsRingWithoutOne.isCommutativeMagma
d_isCommutativeMagma_2346 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRingWithoutOne.isCommutativeMonoid
d_isCommutativeMonoid_2348 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRingWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_2350 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRingWithoutOne.isGroup
d_isGroup_2352 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_2352 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
         (coe v0))
-- Data.Bool.Properties._.IsRingWithoutOne.isInvertibleMagma
d_isInvertibleMagma_2354 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRingWithoutOne.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2356 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRingWithoutOne.isMagma
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
-- Data.Bool.Properties._.IsRingWithoutOne.isMonoid
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
-- Data.Bool.Properties._.IsRingWithoutOne.isSemigroup
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
-- Data.Bool.Properties._.IsRingWithoutOne.isUnitalMagma
d_isUnitalMagma_2364 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRingWithoutOne.⁻¹-cong
d_'8315''185''45'cong_2366 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2366 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.inverse
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
-- Data.Bool.Properties._.IsRingWithoutOne.inverseʳ
d_inverse'691'_2370 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_2370 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.inverseˡ
d_inverse'737'_2372 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_2372 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.distrib
d_distrib_2374 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2374 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2392 (coe v0)
-- Data.Bool.Properties._.IsRingWithoutOne.distribʳ
d_distrib'691'_2376 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2376 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.distribˡ
d_distrib'737'_2378 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2378 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.isEquivalence
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
-- Data.Bool.Properties._.IsRingWithoutOne.isNearSemiring
d_isNearSemiring_2382 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2382
  = coe MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470
-- Data.Bool.Properties._.IsRingWithoutOne.isPartialEquivalence
d_isPartialEquivalence_2384 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRingWithoutOne.refl
d_refl_2386 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2386 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.reflexive
d_reflexive_2388 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2388 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.setoid
d_setoid_2390 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsRingWithoutOne.sym
d_sym_2392 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2392 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.trans
d_trans_2394 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2394 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2396 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2396 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2398 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2398 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.zero
d_zero_2400 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2400 = coe MAlonzo.Code.Algebra.Structures.du_zero_2468
-- Data.Bool.Properties._.IsRingWithoutOne.zeroʳ
d_zero'691'_2402 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2402 = erased
-- Data.Bool.Properties._.IsRingWithoutOne.zeroˡ
d_zero'737'_2404 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2404 = erased
-- Data.Bool.Properties._.IsSelectiveMagma.isEquivalence
d_isEquivalence_2408 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2408 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0))
-- Data.Bool.Properties._.IsSelectiveMagma.isMagma
d_isMagma_2410 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2410 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0)
-- Data.Bool.Properties._.IsSelectiveMagma.isPartialEquivalence
d_isPartialEquivalence_2412 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsSelectiveMagma.refl
d_refl_2414 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2414 = erased
-- Data.Bool.Properties._.IsSelectiveMagma.reflexive
d_reflexive_2416 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2416 = erased
-- Data.Bool.Properties._.IsSelectiveMagma.sel
d_sel_2418 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_2418 v0
  = coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0)
-- Data.Bool.Properties._.IsSelectiveMagma.setoid
d_setoid_2420 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsSelectiveMagma.sym
d_sym_2422 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2422 = erased
-- Data.Bool.Properties._.IsSelectiveMagma.trans
d_trans_2424 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2424 = erased
-- Data.Bool.Properties._.IsSelectiveMagma.∙-cong
d_'8729''45'cong_2426 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2426 = erased
-- Data.Bool.Properties._.IsSelectiveMagma.∙-congʳ
d_'8729''45'cong'691'_2428 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2428 = erased
-- Data.Bool.Properties._.IsSelectiveMagma.∙-congˡ
d_'8729''45'cong'737'_2430 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2430 = erased
-- Data.Bool.Properties._.IsSemigroup.assoc
d_assoc_2434 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2434 = erased
-- Data.Bool.Properties._.IsSemigroup.isEquivalence
d_isEquivalence_2436 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2436 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0))
-- Data.Bool.Properties._.IsSemigroup.isMagma
d_isMagma_2438 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2438 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Data.Bool.Properties._.IsSemigroup.isPartialEquivalence
d_isPartialEquivalence_2440 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsSemigroup.refl
d_refl_2442 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2442 = erased
-- Data.Bool.Properties._.IsSemigroup.reflexive
d_reflexive_2444 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2444 = erased
-- Data.Bool.Properties._.IsSemigroup.setoid
d_setoid_2446 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsSemigroup.sym
d_sym_2448 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2448 = erased
-- Data.Bool.Properties._.IsSemigroup.trans
d_trans_2450 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2450 = erased
-- Data.Bool.Properties._.IsSemigroup.∙-cong
d_'8729''45'cong_2452 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2452 = erased
-- Data.Bool.Properties._.IsSemigroup.∙-congʳ
d_'8729''45'cong'691'_2454 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2454 = erased
-- Data.Bool.Properties._.IsSemigroup.∙-congˡ
d_'8729''45'cong'737'_2456 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2456 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.isEquivalence
d_isEquivalence_2460 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2460 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0))
-- Data.Bool.Properties._.IsSemimedialMagma.isMagma
d_isMagma_2462 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2462 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0)
-- Data.Bool.Properties._.IsSemimedialMagma.isPartialEquivalence
d_isPartialEquivalence_2464 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsSemimedialMagma.refl
d_refl_2466 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2466 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.reflexive
d_reflexive_2468 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2468 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.semiMedial
d_semiMedial_2470 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_2470 v0
  = coe MAlonzo.Code.Algebra.Structures.d_semiMedial_418 (coe v0)
-- Data.Bool.Properties._.IsSemimedialMagma.semimedialʳ
d_semimedial'691'_2472 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'691'_2472 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.semimedialˡ
d_semimedial'737'_2474 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'737'_2474 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.setoid
d_setoid_2476 ::
  (Bool -> Bool -> Bool) ->
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
-- Data.Bool.Properties._.IsSemimedialMagma.sym
d_sym_2478 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2478 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.trans
d_trans_2480 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2480 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.∙-cong
d_'8729''45'cong_2482 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2482 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.∙-congʳ
d_'8729''45'cong'691'_2484 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2484 = erased
-- Data.Bool.Properties._.IsSemimedialMagma.∙-congˡ
d_'8729''45'cong'737'_2486 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2486 = erased
-- Data.Bool.Properties._.IsSemiring.*-assoc
d_'42''45'assoc_2490 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2490 = erased
-- Data.Bool.Properties._.IsSemiring.*-cong
d_'42''45'cong_2492 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2492 = erased
-- Data.Bool.Properties._.IsSemiring.∙-congʳ
d_'8729''45'cong'691'_2494 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2494 = erased
-- Data.Bool.Properties._.IsSemiring.∙-congˡ
d_'8729''45'cong'737'_2496 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2496 = erased
-- Data.Bool.Properties._.IsSemiring.*-identity
d_'42''45'identity_2498 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2498 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Bool.Properties._.IsSemiring.identityʳ
d_identity'691'_2500 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2500 = erased
-- Data.Bool.Properties._.IsSemiring.identityˡ
d_identity'737'_2502 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2502 = erased
-- Data.Bool.Properties._.IsSemiring.*-isMagma
d_'42''45'isMagma_2504 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.*-isMonoid
d_'42''45'isMonoid_2506 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.*-isSemigroup
d_'42''45'isSemigroup_2508 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.assoc
d_assoc_2510 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2510 = erased
-- Data.Bool.Properties._.IsSemiring.comm
d_comm_2512 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2512 = erased
-- Data.Bool.Properties._.IsSemiring.∙-cong
d_'8729''45'cong_2514 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2514 = erased
-- Data.Bool.Properties._.IsSemiring.∙-congʳ
d_'8729''45'cong'691'_2516 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2516 = erased
-- Data.Bool.Properties._.IsSemiring.∙-congˡ
d_'8729''45'cong'737'_2518 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2518 = erased
-- Data.Bool.Properties._.IsSemiring.identity
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
-- Data.Bool.Properties._.IsSemiring.identityʳ
d_identity'691'_2522 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2522 = erased
-- Data.Bool.Properties._.IsSemiring.identityˡ
d_identity'737'_2524 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2524 = erased
-- Data.Bool.Properties._.IsSemiring.isCommutativeMagma
d_isCommutativeMagma_2526 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2528 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2528 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Bool.Properties._.IsSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_2530 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.isMagma
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
-- Data.Bool.Properties._.IsSemiring.isMonoid
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
-- Data.Bool.Properties._.IsSemiring.isSemigroup
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
-- Data.Bool.Properties._.IsSemiring.isUnitalMagma
d_isUnitalMagma_2538 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.distrib
d_distrib_2540 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2540 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Bool.Properties._.IsSemiring.distribʳ
d_distrib'691'_2542 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2542 = erased
-- Data.Bool.Properties._.IsSemiring.distribˡ
d_distrib'737'_2544 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2544 = erased
-- Data.Bool.Properties._.IsSemiring.isEquivalence
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
-- Data.Bool.Properties._.IsSemiring.isNearSemiring
d_isNearSemiring_2548 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.isPartialEquivalence
d_isPartialEquivalence_2550 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2552 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2552 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe v0)
-- Data.Bool.Properties._.IsSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_2554 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2554 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730 v4
-- Data.Bool.Properties._.IsSemiring.refl
d_refl_2556 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2556 = erased
-- Data.Bool.Properties._.IsSemiring.reflexive
d_reflexive_2558 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2558 = erased
-- Data.Bool.Properties._.IsSemiring.setoid
d_setoid_2560 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiring.sym
d_sym_2562 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2562 = erased
-- Data.Bool.Properties._.IsSemiring.trans
d_trans_2564 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2564 = erased
-- Data.Bool.Properties._.IsSemiring.zero
d_zero_2566 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2566 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1656 (coe v0)
-- Data.Bool.Properties._.IsSemiring.zeroʳ
d_zero'691'_2568 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2568 = erased
-- Data.Bool.Properties._.IsSemiring.zeroˡ
d_zero'737'_2570 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2570 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2574 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2574 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2576 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2576 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congʳ
d_'8729''45'cong'691'_2578 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2578 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congˡ
d_'8729''45'cong'737'_2580 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2580 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2582 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2582 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562 (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.identityʳ
d_identity'691'_2584 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2584 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.identityˡ
d_identity'737'_2586 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2586 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-isMagma
d_'42''45'isMagma_2588 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2588 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614 v4
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-isMonoid
d_'42''45'isMonoid_2590 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2590 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618 v4
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.*-isSemigroup
d_'42''45'isSemigroup_2592 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2592 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616 v4
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.assoc
d_assoc_2594 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2594 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.comm
d_comm_2596 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2596 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.∙-cong
d_'8729''45'cong_2598 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2598 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congʳ
d_'8729''45'cong'691'_2600 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2600 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congˡ
d_'8729''45'cong'737'_2602 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2602 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.identity
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.identityʳ
d_identity'691'_2606 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2606 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.identityˡ
d_identity'737'_2608 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2608 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isCommutativeMagma
d_isCommutativeMagma_2610 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2612 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2612 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isCommutativeSemigroup
d_isCommutativeSemigroup_2614 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isMagma
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isMonoid
d_isMonoid_2618 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2618 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe v0))
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isSemigroup
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isUnitalMagma
d_isUnitalMagma_2622 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2624 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2624 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1564 (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.distribʳ
d_distrib'691'_2626 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2626 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.distribˡ
d_distrib'737'_2628 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2628 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isEquivalence
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.isPartialEquivalence
d_isPartialEquivalence_2632 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.refl
d_refl_2634 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2634 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.reflexive
d_reflexive_2636 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2636 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.setoid
d_setoid_2638 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.sym
d_sym_2640 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2640 = erased
-- Data.Bool.Properties._.IsSemiringWithoutAnnihilatingZero.trans
d_trans_2642 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2642 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2646 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2646 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2648 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2648 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2650 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2650 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2652 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2652 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_2654 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2654 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1410 v3
-- Data.Bool.Properties._.IsSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2656 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2656 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1412 v3
-- Data.Bool.Properties._.IsSemiringWithoutOne.assoc
d_assoc_2658 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2658 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.comm
d_comm_2660 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2660 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.∙-cong
d_'8729''45'cong_2662 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2662 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2664 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2664 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2666 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2666 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.identity
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
-- Data.Bool.Properties._.IsSemiringWithoutOne.identityʳ
d_identity'691'_2670 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2670 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.identityˡ
d_identity'737'_2672 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2672 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_2674 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2676 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2676 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_2678 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutOne.isMonoid
d_isMonoid_2680 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2680 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe v0))
-- Data.Bool.Properties._.IsSemiringWithoutOne.distrib
d_distrib_2682 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2682 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1366 (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutOne.distribʳ
d_distrib'691'_2684 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2684 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.distribˡ
d_distrib'737'_2686 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2686 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.isEquivalence
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
-- Data.Bool.Properties._.IsSemiringWithoutOne.isNearSemiring
d_isNearSemiring_2690 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2690 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428 v3
-- Data.Bool.Properties._.IsSemiringWithoutOne.isPartialEquivalence
d_isPartialEquivalence_2692 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutOne.refl
d_refl_2694 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2694 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.reflexive
d_reflexive_2696 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2696 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.setoid
d_setoid_2698 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsSemiringWithoutOne.sym
d_sym_2700 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2700 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.trans
d_trans_2702 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2702 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.zero
d_zero_2704 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2704 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1368 (coe v0)
-- Data.Bool.Properties._.IsSemiringWithoutOne.zeroʳ
d_zero'691'_2706 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2706 = erased
-- Data.Bool.Properties._.IsSemiringWithoutOne.zeroˡ
d_zero'737'_2708 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2708 = erased
-- Data.Bool.Properties._.IsSuccessorSet.isEquivalence
d_isEquivalence_2712 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2712 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_156 (coe v0)
-- Data.Bool.Properties._.IsSuccessorSet.isPartialEquivalence
d_isPartialEquivalence_2714 ::
  (Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsSuccessorSet.refl
d_refl_2716 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2716 = erased
-- Data.Bool.Properties._.IsSuccessorSet.reflexive
d_reflexive_2718 ::
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2718 = erased
-- Data.Bool.Properties._.IsSuccessorSet.setoid
d_setoid_2720 ::
  (Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2720 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_setoid_172 v2
-- Data.Bool.Properties._.IsSuccessorSet.suc#-cong
d_suc'35''45'cong_2722 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'35''45'cong_2722 = erased
-- Data.Bool.Properties._.IsSuccessorSet.sym
d_sym_2724 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2724 = erased
-- Data.Bool.Properties._.IsSuccessorSet.trans
d_trans_2726 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2726 = erased
-- Data.Bool.Properties._.IsUnitalMagma.identity
d_identity_2730 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2730 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_678 (coe v0)
-- Data.Bool.Properties._.IsUnitalMagma.identityʳ
d_identity'691'_2732 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2732 = erased
-- Data.Bool.Properties._.IsUnitalMagma.identityˡ
d_identity'737'_2734 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2734 = erased
-- Data.Bool.Properties._.IsUnitalMagma.isEquivalence
d_isEquivalence_2736 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2736 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0))
-- Data.Bool.Properties._.IsUnitalMagma.isMagma
d_isMagma_2738 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2738 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0)
-- Data.Bool.Properties._.IsUnitalMagma.isPartialEquivalence
d_isPartialEquivalence_2740 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsUnitalMagma.refl
d_refl_2742 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2742 = erased
-- Data.Bool.Properties._.IsUnitalMagma.reflexive
d_reflexive_2744 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2744 = erased
-- Data.Bool.Properties._.IsUnitalMagma.setoid
d_setoid_2746 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
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
-- Data.Bool.Properties._.IsUnitalMagma.sym
d_sym_2748 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2748 = erased
-- Data.Bool.Properties._.IsUnitalMagma.trans
d_trans_2750 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2750 = erased
-- Data.Bool.Properties._.IsUnitalMagma.∙-cong
d_'8729''45'cong_2752 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2752 = erased
-- Data.Bool.Properties._.IsUnitalMagma.∙-congʳ
d_'8729''45'cong'691'_2754 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2754 = erased
-- Data.Bool.Properties._.IsUnitalMagma.∙-congˡ
d_'8729''45'cong'737'_2756 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2756 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra
d_IsBooleanAlgebra_2760 a0 a1 a2 a3 a4 = ()
-- Data.Bool.Properties._.IsBoundedJoinSemilattice
d_IsBoundedJoinSemilattice_2764 ::
  (Bool -> Bool -> Bool) -> Bool -> ()
d_IsBoundedJoinSemilattice_2764 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice
d_IsBoundedMeetSemilattice_2766 ::
  (Bool -> Bool -> Bool) -> Bool -> ()
d_IsBoundedMeetSemilattice_2766 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice
d_IsBoundedSemilattice_2768 :: (Bool -> Bool -> Bool) -> Bool -> ()
d_IsBoundedSemilattice_2768 = erased
-- Data.Bool.Properties._.IsDistributiveLattice
d_IsDistributiveLattice_2770 a0 a1 = ()
-- Data.Bool.Properties._.IsJoinSemilattice
d_IsJoinSemilattice_2774 :: (Bool -> Bool -> Bool) -> ()
d_IsJoinSemilattice_2774 = erased
-- Data.Bool.Properties._.IsLattice
d_IsLattice_2776 a0 a1 = ()
-- Data.Bool.Properties._.IsMeetSemilattice
d_IsMeetSemilattice_2780 :: (Bool -> Bool -> Bool) -> ()
d_IsMeetSemilattice_2780 = erased
-- Data.Bool.Properties._.IsSemilattice
d_IsSemilattice_2782 :: (Bool -> Bool -> Bool) -> ()
d_IsSemilattice_2782 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.absorptive
d_absorptive_2786 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_2786 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe v0)))
-- Data.Bool.Properties._.IsBooleanAlgebra.isDistributiveLattice
d_isDistributiveLattice_2788 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_isDistributiveLattice_2788 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
      (coe v0)
-- Data.Bool.Properties._.IsBooleanAlgebra.isEquivalence
d_isEquivalence_2790 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2790 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe v0)))
-- Data.Bool.Properties._.IsBooleanAlgebra.isLattice
d_isLattice_2792 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_isLattice_2792 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
         (coe v0))
-- Data.Bool.Properties._.IsBooleanAlgebra.isPartialEquivalence
d_isPartialEquivalence_2794 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2794 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_2794 v5
du_isPartialEquivalence_2794 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2794 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe v2))))
-- Data.Bool.Properties._.IsBooleanAlgebra.refl
d_refl_2796 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2796 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.reflexive
d_reflexive_2798 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2798 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.sym
d_sym_2800 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2800 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.trans
d_trans_2802 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2802 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.¬-cong
d_'172''45'cong_2804 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172''45'cong_2804 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_2806 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'absorbs'45''8744'_2806 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-assoc
d_'8743''45'assoc_2808 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_2808 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-comm
d_'8743''45'comm_2810 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_2810 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-complement
d_'8743''45'complement_2812 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_2812 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3248
      (coe v0)
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-complementʳ
d_'8743''45'complement'691'_2814 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'complement'691'_2814 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-complementˡ
d_'8743''45'complement'737'_2816 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'complement'737'_2816 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-cong
d_'8743''45'cong_2818 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong_2818 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-congʳ
d_'8743''45'cong'691'_2820 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong'691'_2820 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-congˡ
d_'8743''45'cong'737'_2822 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong'737'_2822 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-distrib-∨
d_'8743''45'distrib'45''8744'_2824 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_2824 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3162
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
         (coe v0))
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_2826 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'691''45''8744'_2826 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_2828 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'737''45''8744'_2828 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_2830 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'absorbs'45''8743'_2830 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-assoc
d_'8744''45'assoc_2832 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_2832 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-comm
d_'8744''45'comm_2834 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_2834 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-complement
d_'8744''45'complement_2836 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_2836 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3246
      (coe v0)
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-complementʳ
d_'8744''45'complement'691'_2838 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'complement'691'_2838 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-complementˡ
d_'8744''45'complement'737'_2840 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'complement'737'_2840 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-cong
d_'8744''45'cong_2842 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong_2842 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-congʳ
d_'8744''45'cong'691'_2844 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong'691'_2844 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-congˡ
d_'8744''45'cong'737'_2846 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong'737'_2846 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-distrib-∧
d_'8744''45'distrib'45''8743'_2848 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_2848 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3160
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
         (coe v0))
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_2850 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'691''45''8743'_2850 = erased
-- Data.Bool.Properties._.IsBooleanAlgebra.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_2852 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool) ->
  Bool ->
  Bool ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'737''45''8743'_2852 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.assoc
d_assoc_2856 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2856 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.comm
d_comm_2858 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2858 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.idem
d_idem_2860 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_2860 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.identity
d_identity_2862 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2862 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.identityʳ
d_identity'691'_2864 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2864 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.identityˡ
d_identity'737'_2866 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2866 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isBand
d_isBand_2868 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_2868 ~v0 ~v1 v2 = du_isBand_2868 v2
du_isBand_2868 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_2868 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isEquivalence
d_isEquivalence_2870 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2870 ~v0 ~v1 v2 = du_isEquivalence_2870 v2
du_isEquivalence_2870 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2870 v0
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
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isCommutativeBand
d_isCommutativeBand_2872 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_2872 ~v0 ~v1 v2 = du_isCommutativeBand_2872 v2
du_isCommutativeBand_2872 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_2872 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v0)
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isMagma
d_isMagma_2874 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2874 ~v0 ~v1 v2 = du_isMagma_2874 v2
du_isMagma_2874 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2874 v0
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
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isPartialEquivalence
d_isPartialEquivalence_2876 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2876 ~v0 ~v1 v2
  = du_isPartialEquivalence_2876 v2
du_isPartialEquivalence_2876 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2876 v0
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
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.isSemigroup
d_isSemigroup_2878 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2878 ~v0 ~v1 v2 = du_isSemigroup_2878 v2
du_isSemigroup_2878 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2878 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.refl
d_refl_2880 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2880 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.reflexive
d_reflexive_2882 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2882 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.setoid
d_setoid_2884 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2884 ~v0 ~v1 v2 = du_setoid_2884 v2
du_setoid_2884 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2884 v0
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
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.sym
d_sym_2886 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2886 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.trans
d_trans_2888 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2888 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.∙-cong
d_'8729''45'cong_2890 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2890 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.∙-congʳ
d_'8729''45'cong'691'_2892 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2892 = erased
-- Data.Bool.Properties._.IsBoundedJoinSemilattice.∙-congˡ
d_'8729''45'cong'737'_2894 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2894 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.assoc
d_assoc_2898 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2898 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.comm
d_comm_2900 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2900 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.idem
d_idem_2902 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_2902 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.identity
d_identity_2904 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2904 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.identityʳ
d_identity'691'_2906 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2906 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.identityˡ
d_identity'737'_2908 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2908 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isBand
d_isBand_2910 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_2910 ~v0 ~v1 v2 = du_isBand_2910 v2
du_isBand_2910 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_2910 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isEquivalence
d_isEquivalence_2912 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2912 ~v0 ~v1 v2 = du_isEquivalence_2912 v2
du_isEquivalence_2912 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2912 v0
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
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isMagma
d_isMagma_2914 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2914 ~v0 ~v1 v2 = du_isMagma_2914 v2
du_isMagma_2914 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2914 v0
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
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isCommutativeBand
d_isCommutativeBand_2916 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_2916 ~v0 ~v1 v2 = du_isCommutativeBand_2916 v2
du_isCommutativeBand_2916 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_2916 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v0)
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isPartialEquivalence
d_isPartialEquivalence_2918 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2918 ~v0 ~v1 v2
  = du_isPartialEquivalence_2918 v2
du_isPartialEquivalence_2918 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2918 v0
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
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.isSemigroup
d_isSemigroup_2920 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2920 ~v0 ~v1 v2 = du_isSemigroup_2920 v2
du_isSemigroup_2920 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2920 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.refl
d_refl_2922 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2922 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.reflexive
d_reflexive_2924 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2924 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.setoid
d_setoid_2926 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2926 ~v0 ~v1 v2 = du_setoid_2926 v2
du_setoid_2926 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2926 v0
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
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.sym
d_sym_2928 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2928 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.trans
d_trans_2930 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2930 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.∙-cong
d_'8729''45'cong_2932 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2932 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.∙-congʳ
d_'8729''45'cong'691'_2934 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2934 = erased
-- Data.Bool.Properties._.IsBoundedMeetSemilattice.∙-congˡ
d_'8729''45'cong'737'_2936 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2936 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.assoc
d_assoc_2940 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2940 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.comm
d_comm_2942 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2942 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.idem
d_idem_2944 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_2944 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.identity
d_identity_2946 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2946 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Bool.Properties._.IsBoundedSemilattice.identityʳ
d_identity'691'_2948 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2948 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.identityˡ
d_identity'737'_2950 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2950 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.isBand
d_isBand_2952 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_2952 ~v0 ~v1 v2 = du_isBand_2952 v2
du_isBand_2952 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_2952 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Data.Bool.Properties._.IsBoundedSemilattice.isCommutativeMagma
d_isCommutativeMagma_2954 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2954 ~v0 ~v1 v2
  = du_isCommutativeMagma_2954 v2
du_isCommutativeMagma_2954 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2954 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Bool.Properties._.IsBoundedSemilattice.isCommutativeMonoid
d_isCommutativeMonoid_2956 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2956 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0)
-- Data.Bool.Properties._.IsBoundedSemilattice.isCommutativeSemigroup
d_isCommutativeSemigroup_2958 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2958 ~v0 ~v1 v2
  = du_isCommutativeSemigroup_2958 v2
du_isCommutativeSemigroup_2958 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2958 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Bool.Properties._.IsBoundedSemilattice.isEquivalence
d_isEquivalence_2960 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2960 v0
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
-- Data.Bool.Properties._.IsBoundedSemilattice.isIdempotentMonoid
d_isIdempotentMonoid_2962 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_2962 ~v0 ~v1 v2
  = du_isIdempotentMonoid_2962 v2
du_isIdempotentMonoid_2962 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_2962 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0)
-- Data.Bool.Properties._.IsBoundedSemilattice.isMagma
d_isMagma_2964 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2964 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
               (coe v0))))
-- Data.Bool.Properties._.IsBoundedSemilattice.isMonoid
d_isMonoid_2966 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2966 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Bool.Properties._.IsBoundedSemilattice.isPartialEquivalence
d_isPartialEquivalence_2968 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2968 ~v0 ~v1 v2
  = du_isPartialEquivalence_2968 v2
du_isPartialEquivalence_2968 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2968 v0
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
-- Data.Bool.Properties._.IsBoundedSemilattice.isSemigroup
d_isSemigroup_2970 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2970 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Bool.Properties._.IsBoundedSemilattice.isCommutativeBand
d_isCommutativeBand_2972 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_2972 ~v0 ~v1 v2 = du_isCommutativeBand_2972 v2
du_isCommutativeBand_2972 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_2972 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v0)
-- Data.Bool.Properties._.IsBoundedSemilattice.isUnitalMagma
d_isUnitalMagma_2974 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2974 ~v0 ~v1 v2 = du_isUnitalMagma_2974 v2
du_isUnitalMagma_2974 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2974 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Data.Bool.Properties._.IsBoundedSemilattice.refl
d_refl_2976 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2976 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.reflexive
d_reflexive_2978 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2978 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.setoid
d_setoid_2980 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2980 ~v0 ~v1 v2 = du_setoid_2980 v2
du_setoid_2980 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2980 v0
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
-- Data.Bool.Properties._.IsBoundedSemilattice.sym
d_sym_2982 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2982 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.trans
d_trans_2984 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2984 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.∙-cong
d_'8729''45'cong_2986 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2986 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.∙-congʳ
d_'8729''45'cong'691'_2988 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2988 = erased
-- Data.Bool.Properties._.IsBoundedSemilattice.∙-congˡ
d_'8729''45'cong'737'_2990 ::
  (Bool -> Bool -> Bool) ->
  Bool ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2990 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.absorptive
d_absorptive_2994 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_2994 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v0))
-- Data.Bool.Properties._.IsDistributiveLattice.isEquivalence
d_isEquivalence_2996 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2996 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v0))
-- Data.Bool.Properties._.IsDistributiveLattice.isLattice
d_isLattice_2998 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_isLattice_2998 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v0)
-- Data.Bool.Properties._.IsDistributiveLattice.isPartialEquivalence
d_isPartialEquivalence_3000 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3000 ~v0 ~v1 v2
  = du_isPartialEquivalence_3000 v2
du_isPartialEquivalence_3000 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3000 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
            (coe v1)))
-- Data.Bool.Properties._.IsDistributiveLattice.refl
d_refl_3002 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_3002 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.reflexive
d_reflexive_3004 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_3004 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.sym
d_sym_3006 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_3006 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.trans
d_trans_3008 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_3008 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_3010 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'absorbs'45''8744'_3010 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-assoc
d_'8743''45'assoc_3012 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_3012 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-comm
d_'8743''45'comm_3014 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_3014 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-cong
d_'8743''45'cong_3016 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong_3016 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-congʳ
d_'8743''45'cong'691'_3018 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong'691'_3018 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-congˡ
d_'8743''45'cong'737'_3020 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong'737'_3020 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-distrib-∨
d_'8743''45'distrib'45''8744'_3022 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_3022 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3162
      (coe v0)
-- Data.Bool.Properties._.IsDistributiveLattice.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_3024 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'691''45''8744'_3024 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_3026 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'737''45''8744'_3026 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_3028 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'absorbs'45''8743'_3028 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-assoc
d_'8744''45'assoc_3030 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_3030 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-comm
d_'8744''45'comm_3032 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_3032 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-cong
d_'8744''45'cong_3034 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong_3034 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-congʳ
d_'8744''45'cong'691'_3036 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong'691'_3036 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-congˡ
d_'8744''45'cong'737'_3038 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong'737'_3038 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-distrib-∧
d_'8744''45'distrib'45''8743'_3040 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_3040 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3160
      (coe v0)
-- Data.Bool.Properties._.IsDistributiveLattice.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_3042 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'691''45''8743'_3042 = erased
-- Data.Bool.Properties._.IsDistributiveLattice.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_3044 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'737''45''8743'_3044 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.assoc
d_assoc_3048 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_3048 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.comm
d_comm_3050 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_3050 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.idem
d_idem_3052 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_3052 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.isBand
d_isBand_3054 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_3054 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Data.Bool.Properties._.IsJoinSemilattice.isEquivalence
d_isEquivalence_3056 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3056 ~v0 v1 = du_isEquivalence_3056 v1
du_isEquivalence_3056 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_3056 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Data.Bool.Properties._.IsJoinSemilattice.isMagma
d_isMagma_3058 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_3058 ~v0 v1 = du_isMagma_3058 v1
du_isMagma_3058 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_3058 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Data.Bool.Properties._.IsJoinSemilattice.isPartialEquivalence
d_isPartialEquivalence_3060 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3060 ~v0 v1
  = du_isPartialEquivalence_3060 v1
du_isPartialEquivalence_3060 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3060 v0
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
-- Data.Bool.Properties._.IsJoinSemilattice.isSemigroup
d_isSemigroup_3062 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_3062 ~v0 v1 = du_isSemigroup_3062 v1
du_isSemigroup_3062 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_3062 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Data.Bool.Properties._.IsJoinSemilattice.refl
d_refl_3064 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_3064 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.reflexive
d_reflexive_3066 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_3066 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.setoid
d_setoid_3068 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3068 ~v0 v1 = du_setoid_3068 v1
du_setoid_3068 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3068 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Bool.Properties._.IsJoinSemilattice.sym
d_sym_3070 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_3070 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.trans
d_trans_3072 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_3072 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.∙-cong
d_'8729''45'cong_3074 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_3074 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.∙-congʳ
d_'8729''45'cong'691'_3076 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_3076 = erased
-- Data.Bool.Properties._.IsJoinSemilattice.∙-congˡ
d_'8729''45'cong'737'_3078 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_3078 = erased
-- Data.Bool.Properties._.IsLattice.absorptive
d_absorptive_3082 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_3082 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106 (coe v0)
-- Data.Bool.Properties._.IsLattice.isEquivalence
d_isEquivalence_3084 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3084 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
      (coe v0)
-- Data.Bool.Properties._.IsLattice.isPartialEquivalence
d_isPartialEquivalence_3086 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3086 ~v0 ~v1 v2
  = du_isPartialEquivalence_3086 v2
du_isPartialEquivalence_3086 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3086 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe v0))
-- Data.Bool.Properties._.IsLattice.refl
d_refl_3088 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_3088 = erased
-- Data.Bool.Properties._.IsLattice.reflexive
d_reflexive_3090 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_3090 = erased
-- Data.Bool.Properties._.IsLattice.sym
d_sym_3092 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_3092 = erased
-- Data.Bool.Properties._.IsLattice.trans
d_trans_3094 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_3094 = erased
-- Data.Bool.Properties._.IsLattice.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_3096 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'absorbs'45''8744'_3096 = erased
-- Data.Bool.Properties._.IsLattice.∧-assoc
d_'8743''45'assoc_3098 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_3098 = erased
-- Data.Bool.Properties._.IsLattice.∧-comm
d_'8743''45'comm_3100 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_3100 = erased
-- Data.Bool.Properties._.IsLattice.∧-cong
d_'8743''45'cong_3102 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong_3102 = erased
-- Data.Bool.Properties._.IsLattice.∧-congʳ
d_'8743''45'cong'691'_3104 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong'691'_3104 = erased
-- Data.Bool.Properties._.IsLattice.∧-congˡ
d_'8743''45'cong'737'_3106 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong'737'_3106 = erased
-- Data.Bool.Properties._.IsLattice.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_3108 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'absorbs'45''8743'_3108 = erased
-- Data.Bool.Properties._.IsLattice.∨-assoc
d_'8744''45'assoc_3110 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_3110 = erased
-- Data.Bool.Properties._.IsLattice.∨-comm
d_'8744''45'comm_3112 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_3112 = erased
-- Data.Bool.Properties._.IsLattice.∨-cong
d_'8744''45'cong_3114 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong_3114 = erased
-- Data.Bool.Properties._.IsLattice.∨-congʳ
d_'8744''45'cong'691'_3116 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong'691'_3116 = erased
-- Data.Bool.Properties._.IsLattice.∨-congˡ
d_'8744''45'cong'737'_3118 ::
  (Bool -> Bool -> Bool) ->
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong'737'_3118 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.assoc
d_assoc_3122 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_3122 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.comm
d_comm_3124 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_3124 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.idem
d_idem_3126 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_3126 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.isBand
d_isBand_3128 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_3128 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Data.Bool.Properties._.IsMeetSemilattice.isEquivalence
d_isEquivalence_3130 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3130 ~v0 v1 = du_isEquivalence_3130 v1
du_isEquivalence_3130 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_3130 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Data.Bool.Properties._.IsMeetSemilattice.isMagma
d_isMagma_3132 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_3132 ~v0 v1 = du_isMagma_3132 v1
du_isMagma_3132 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_3132 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Data.Bool.Properties._.IsMeetSemilattice.isPartialEquivalence
d_isPartialEquivalence_3134 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3134 ~v0 v1
  = du_isPartialEquivalence_3134 v1
du_isPartialEquivalence_3134 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3134 v0
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
-- Data.Bool.Properties._.IsMeetSemilattice.isSemigroup
d_isSemigroup_3136 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_3136 ~v0 v1 = du_isSemigroup_3136 v1
du_isSemigroup_3136 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_3136 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Data.Bool.Properties._.IsMeetSemilattice.refl
d_refl_3138 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_3138 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.reflexive
d_reflexive_3140 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_3140 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.setoid
d_setoid_3142 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3142 ~v0 v1 = du_setoid_3142 v1
du_setoid_3142 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3142 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Bool.Properties._.IsMeetSemilattice.sym
d_sym_3144 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_3144 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.trans
d_trans_3146 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_3146 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.∙-cong
d_'8729''45'cong_3148 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_3148 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.∙-congʳ
d_'8729''45'cong'691'_3150 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_3150 = erased
-- Data.Bool.Properties._.IsMeetSemilattice.∙-congˡ
d_'8729''45'cong'737'_3152 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_3152 = erased
-- Data.Bool.Properties._.IsSemilattice.assoc
d_assoc_3156 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_3156 = erased
-- Data.Bool.Properties._.IsSemilattice.comm
d_comm_3158 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_3158 = erased
-- Data.Bool.Properties._.IsSemilattice.idem
d_idem_3160 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_3160 = erased
-- Data.Bool.Properties._.IsSemilattice.isBand
d_isBand_3162 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_3162 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Data.Bool.Properties._.IsSemilattice.isEquivalence
d_isEquivalence_3164 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_3164 ~v0 v1 = du_isEquivalence_3164 v1
du_isEquivalence_3164 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_3164 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Data.Bool.Properties._.IsSemilattice.isMagma
d_isMagma_3166 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_3166 ~v0 v1 = du_isMagma_3166 v1
du_isMagma_3166 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_3166 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Data.Bool.Properties._.IsSemilattice.isPartialEquivalence
d_isPartialEquivalence_3168 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_3168 ~v0 v1
  = du_isPartialEquivalence_3168 v1
du_isPartialEquivalence_3168 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_3168 v0
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
-- Data.Bool.Properties._.IsSemilattice.isSemigroup
d_isSemigroup_3170 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_3170 ~v0 v1 = du_isSemigroup_3170 v1
du_isSemigroup_3170 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_3170 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Data.Bool.Properties._.IsSemilattice.refl
d_refl_3172 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_3172 = erased
-- Data.Bool.Properties._.IsSemilattice.reflexive
d_reflexive_3174 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_3174 = erased
-- Data.Bool.Properties._.IsSemilattice.setoid
d_setoid_3176 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_3176 ~v0 v1 = du_setoid_3176 v1
du_setoid_3176 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_3176 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Bool.Properties._.IsSemilattice.sym
d_sym_3178 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_3178 = erased
-- Data.Bool.Properties._.IsSemilattice.trans
d_trans_3180 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_3180 = erased
-- Data.Bool.Properties._.IsSemilattice.∙-cong
d_'8729''45'cong_3182 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_3182 = erased
-- Data.Bool.Properties._.IsSemilattice.∙-congʳ
d_'8729''45'cong'691'_3184 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_3184 = erased
-- Data.Bool.Properties._.IsSemilattice.∙-congˡ
d_'8729''45'cong'737'_3186 ::
  (Bool -> Bool -> Bool) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_3186 = erased
-- Data.Bool.Properties._≟_
d__'8799'__3196 ::
  Bool ->
  Bool -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__3196 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe v1)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             else coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe v1) (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      else (if coe v1
              then coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe v0) (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
              else coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
-- Data.Bool.Properties.≡-setoid
d_'8801''45'setoid_3198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_3198
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Bool.Properties.≡-decSetoid
d_'8801''45'decSetoid_3200 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_3200
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__3196)
-- Data.Bool.Properties.≤-reflexive
d_'8804''45'reflexive_3202 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'reflexive_3202 ~v0 ~v1 ~v2
  = du_'8804''45'reflexive_3202
du_'8804''45'reflexive_3202 ::
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10
du_'8804''45'reflexive_3202
  = coe MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16
-- Data.Bool.Properties.≤-refl
d_'8804''45'refl_3204 ::
  Bool -> MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'refl_3204 ~v0 = du_'8804''45'refl_3204
du_'8804''45'refl_3204 :: MAlonzo.Code.Data.Bool.Base.T__'8804'__10
du_'8804''45'refl_3204 = coe du_'8804''45'reflexive_3202
-- Data.Bool.Properties.≤-trans
d_'8804''45'trans_3206 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'trans_3206 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45'trans_3206 v3 v4
du_'8804''45'trans_3206 ::
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10
du_'8804''45'trans_3206 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Bool.Base.C_f'8804't_12
        -> coe seq (coe v1) (coe v0)
      MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Bool.Properties.≤-antisym
d_'8804''45'antisym_3210 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_3210 = erased
-- Data.Bool.Properties.≤-minimum
d_'8804''45'minimum_3212 ::
  Bool -> MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'minimum_3212 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Bool.Base.C_f'8804't_12
      else coe MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16
-- Data.Bool.Properties.≤-maximum
d_'8804''45'maximum_3214 ::
  Bool -> MAlonzo.Code.Data.Bool.Base.T__'8804'__10
d_'8804''45'maximum_3214 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16
      else coe MAlonzo.Code.Data.Bool.Base.C_f'8804't_12
-- Data.Bool.Properties.≤-total
d_'8804''45'total_3216 ::
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_3216 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe d_'8804''45'maximum_3214 (coe v1))
      else coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe d_'8804''45'minimum_3212 (coe v1))
-- Data.Bool.Properties._≤?_
d__'8804''63'__3222 ::
  Bool ->
  Bool -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__3222 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe v1)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Data.Bool.Base.C_b'8804'b_16))
             else coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe v1) (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      else coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe d_'8804''45'minimum_3212 (coe v1)))
-- Data.Bool.Properties.≤-irrelevant
d_'8804''45'irrelevant_3226 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_3226 = erased
-- Data.Bool.Properties.≤-isPreorder
d_'8804''45'isPreorder_3228 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8804''45'isPreorder_3228
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_3202)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45'trans_3206 v3 v4)
-- Data.Bool.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_3230 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8804''45'isPartialOrder_3230
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe d_'8804''45'isPreorder_3228) erased
-- Data.Bool.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_3232 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8804''45'isTotalOrder_3232
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe d_'8804''45'isPartialOrder_3230) (coe d_'8804''45'total_3216)
-- Data.Bool.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_3234 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8804''45'isDecTotalOrder_3234
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe d_'8804''45'isTotalOrder_3232) (coe d__'8799'__3196)
      (coe d__'8804''63'__3222)
-- Data.Bool.Properties.≤-poset
d_'8804''45'poset_3236 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8804''45'poset_3236
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      d_'8804''45'isPartialOrder_3230
-- Data.Bool.Properties.≤-preorder
d_'8804''45'preorder_3238 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'8804''45'preorder_3238
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      d_'8804''45'isPreorder_3228
-- Data.Bool.Properties.≤-totalOrder
d_'8804''45'totalOrder_3240 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_'8804''45'totalOrder_3240
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1090
      d_'8804''45'isTotalOrder_3232
-- Data.Bool.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_3242 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_'8804''45'decTotalOrder_3242
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      d_'8804''45'isDecTotalOrder_3234
-- Data.Bool.Properties.<-irrefl
d_'60''45'irrefl_3244 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_3244 = erased
-- Data.Bool.Properties.<-asym
d_'60''45'asym_3246 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_3246 = erased
-- Data.Bool.Properties.<-trans
d_'60''45'trans_3248 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18
d_'60''45'trans_3248 = erased
-- Data.Bool.Properties.<-transʳ
d_'60''45'trans'691'_3250 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18
d_'60''45'trans'691'_3250 = erased
-- Data.Bool.Properties.<-transˡ
d_'60''45'trans'737'_3252 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'8804'__10 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18
d_'60''45'trans'737'_3252 = erased
-- Data.Bool.Properties.<-cmp
d_'60''45'cmp_3254 ::
  Bool -> Bool -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_3254 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
             else coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 erased
      else (if coe v1
              then coe
                     MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 erased
              else coe
                     MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased)
-- Data.Bool.Properties._<?_
d__'60''63'__3256 ::
  Bool ->
  Bool -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__3256 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      else (if coe v1
              then coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe v1)
                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
              else coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                     (coe v1)
                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
-- Data.Bool.Properties.<-resp₂-≡
d_'60''45'resp'8322''45''8801'_3258 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'8322''45''8801'_3258
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Bool.Properties.<-irrelevant
d_'60''45'irrelevant_3264 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_3264 = erased
-- Data.Bool.Properties.<-wellFounded
d_'60''45'wellFounded_3266 ::
  Bool -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''45'wellFounded_3266 = erased
-- Data.Bool.Properties._.<-acc
d_'60''45'acc_3276 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Data.Bool.Base.T__'60'__18 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''45'acc_3276 = erased
-- Data.Bool.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_3278 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_3278
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased d_'60''45'resp'8322''45''8801'_3258
-- Data.Bool.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_3280 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''45'isStrictTotalOrder_3280
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe d_'60''45'isStrictPartialOrder_3278) (coe d_'60''45'cmp_3254)
-- Data.Bool.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_3282 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'60''45'strictPartialOrder_3282
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      d_'60''45'isStrictPartialOrder_3278
-- Data.Bool.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_3284 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_'60''45'strictTotalOrder_3284
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      d_'60''45'isStrictTotalOrder_3280
-- Data.Bool.Properties.∨-assoc
d_'8744''45'assoc_3286 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_3286 = erased
-- Data.Bool.Properties.∨-comm
d_'8744''45'comm_3296 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_3296 = erased
-- Data.Bool.Properties.∨-identityˡ
d_'8744''45'identity'737'_3298 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'identity'737'_3298 = erased
-- Data.Bool.Properties.∨-identityʳ
d_'8744''45'identity'691'_3300 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'identity'691'_3300 = erased
-- Data.Bool.Properties.∨-identity
d_'8744''45'identity_3302 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'identity_3302
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-zeroˡ
d_'8744''45'zero'737'_3304 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'zero'737'_3304 = erased
-- Data.Bool.Properties.∨-zeroʳ
d_'8744''45'zero'691'_3306 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'zero'691'_3306 = erased
-- Data.Bool.Properties.∨-zero
d_'8744''45'zero_3308 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'zero_3308
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-inverseˡ
d_'8744''45'inverse'737'_3310 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'inverse'737'_3310 = erased
-- Data.Bool.Properties.∨-inverseʳ
d_'8744''45'inverse'691'_3312 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'inverse'691'_3312 = erased
-- Data.Bool.Properties.∨-inverse
d_'8744''45'inverse_3316 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'inverse_3316
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-idem
d_'8744''45'idem_3318 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'idem_3318 = erased
-- Data.Bool.Properties.∨-sel
d_'8744''45'sel_3320 ::
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8744''45'sel_3320 v0 ~v1 = du_'8744''45'sel_3320 v0
du_'8744''45'sel_3320 ::
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8744''45'sel_3320 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Bool.Properties.∨-conicalˡ
d_'8744''45'conical'737'_3326 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'conical'737'_3326 = erased
-- Data.Bool.Properties.∨-conicalʳ
d_'8744''45'conical'691'_3328 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'conical'691'_3328 = erased
-- Data.Bool.Properties.∨-conical
d_'8744''45'conical_3330 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'conical_3330
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-isMagma
d_'8744''45'isMagma_3332 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8744''45'isMagma_3332
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Bool.Properties.∨-magma
d_'8744''45'magma_3334 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8744''45'magma_3334
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30 d_'8744''45'isMagma_3332
-- Data.Bool.Properties.∨-isSemigroup
d_'8744''45'isSemigroup_3336 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8744''45'isSemigroup_3336
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe d_'8744''45'isMagma_3332) erased
-- Data.Bool.Properties.∨-semigroup
d_'8744''45'semigroup_3338 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8744''45'semigroup_3338
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      d_'8744''45'isSemigroup_3336
-- Data.Bool.Properties.∨-isBand
d_'8744''45'isBand_3340 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8744''45'isBand_3340
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_564
      (coe d_'8744''45'isSemigroup_3336) erased
-- Data.Bool.Properties.∨-band
d_'8744''45'band_3342 :: MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8744''45'band_3342
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_682
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30 d_'8744''45'isBand_3340
-- Data.Bool.Properties.∨-isSemilattice
d_'8744''45'isSemilattice_3344 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8744''45'isSemilattice_3344
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_660
      (coe d_'8744''45'isBand_3340) erased
-- Data.Bool.Properties.∨-semilattice
d_'8744''45'semilattice_3346 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8744''45'semilattice_3346
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_84
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      d_'8744''45'isSemilattice_3344
-- Data.Bool.Properties.∨-isMonoid
d_'8744''45'isMonoid_3348 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8744''45'isMonoid_3348
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe d_'8744''45'isSemigroup_3336) (coe d_'8744''45'identity_3302)
-- Data.Bool.Properties.∨-isCommutativeMonoid
d_'8744''45'isCommutativeMonoid_3350 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'8744''45'isCommutativeMonoid_3350
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe d_'8744''45'isMonoid_3348) erased
-- Data.Bool.Properties.∨-commutativeMonoid
d_'8744''45'commutativeMonoid_3352 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'8744''45'commutativeMonoid_3352
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      d_'8744''45'isCommutativeMonoid_3350
-- Data.Bool.Properties.∨-isIdempotentCommutativeMonoid
d_'8744''45'isIdempotentCommutativeMonoid_3354 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'8744''45'isIdempotentCommutativeMonoid_3354
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_950
      (coe d_'8744''45'isCommutativeMonoid_3350) erased
-- Data.Bool.Properties.∨-idempotentCommutativeMonoid
d_'8744''45'idempotentCommutativeMonoid_3356 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186
d_'8744''45'idempotentCommutativeMonoid_3356
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1296
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      d_'8744''45'isIdempotentCommutativeMonoid_3354
-- Data.Bool.Properties.∧-assoc
d_'8743''45'assoc_3358 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_3358 = erased
-- Data.Bool.Properties.∧-comm
d_'8743''45'comm_3368 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_3368 = erased
-- Data.Bool.Properties.∧-identityˡ
d_'8743''45'identity'737'_3370 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'identity'737'_3370 = erased
-- Data.Bool.Properties.∧-identityʳ
d_'8743''45'identity'691'_3372 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'identity'691'_3372 = erased
-- Data.Bool.Properties.∧-identity
d_'8743''45'identity_3374 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'identity_3374
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-zeroˡ
d_'8743''45'zero'737'_3376 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'zero'737'_3376 = erased
-- Data.Bool.Properties.∧-zeroʳ
d_'8743''45'zero'691'_3378 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'zero'691'_3378 = erased
-- Data.Bool.Properties.∧-zero
d_'8743''45'zero_3380 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'zero_3380
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-inverseˡ
d_'8743''45'inverse'737'_3382 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'inverse'737'_3382 = erased
-- Data.Bool.Properties.∧-inverseʳ
d_'8743''45'inverse'691'_3384 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'inverse'691'_3384 = erased
-- Data.Bool.Properties.∧-inverse
d_'8743''45'inverse_3388 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'inverse_3388
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-idem
d_'8743''45'idem_3390 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'idem_3390 = erased
-- Data.Bool.Properties.∧-sel
d_'8743''45'sel_3392 ::
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8743''45'sel_3392 v0 ~v1 = du_'8743''45'sel_3392 v0
du_'8743''45'sel_3392 ::
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8743''45'sel_3392 v0
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
      else coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
-- Data.Bool.Properties.∧-conicalˡ
d_'8743''45'conical'737'_3398 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'conical'737'_3398 = erased
-- Data.Bool.Properties.∧-conicalʳ
d_'8743''45'conical'691'_3400 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'conical'691'_3400 = erased
-- Data.Bool.Properties.∧-conical
d_'8743''45'conical_3402 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'conical_3402
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_3404 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'737''45''8744'_3404 = erased
-- Data.Bool.Properties.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_3414 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'691''45''8744'_3414 = erased
-- Data.Bool.Properties.∧-distrib-∨
d_'8743''45'distrib'45''8744'_3422 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_3422
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_3424 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'737''45''8743'_3424 = erased
-- Data.Bool.Properties.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_3434 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'691''45''8743'_3434 = erased
-- Data.Bool.Properties.∨-distrib-∧
d_'8744''45'distrib'45''8743'_3442 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_3442
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-abs-∨
d_'8743''45'abs'45''8744'_3444 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'abs'45''8744'_3444 = erased
-- Data.Bool.Properties.∨-abs-∧
d_'8744''45'abs'45''8743'_3450 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'abs'45''8743'_3450 = erased
-- Data.Bool.Properties.∨-∧-absorptive
d_'8744''45''8743''45'absorptive_3456 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45''8743''45'absorptive_3456
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-isMagma
d_'8743''45'isMagma_3458 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8743''45'isMagma_3458
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Bool.Properties.∧-magma
d_'8743''45'magma_3460 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8743''45'magma_3460
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24 d_'8743''45'isMagma_3458
-- Data.Bool.Properties.∧-isSemigroup
d_'8743''45'isSemigroup_3462 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8743''45'isSemigroup_3462
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe d_'8743''45'isMagma_3458) erased
-- Data.Bool.Properties.∧-semigroup
d_'8743''45'semigroup_3464 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8743''45'semigroup_3464
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      d_'8743''45'isSemigroup_3462
-- Data.Bool.Properties.∧-isBand
d_'8743''45'isBand_3466 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8743''45'isBand_3466
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_564
      (coe d_'8743''45'isSemigroup_3462) erased
-- Data.Bool.Properties.∧-band
d_'8743''45'band_3468 :: MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8743''45'band_3468
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_682
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24 d_'8743''45'isBand_3466
-- Data.Bool.Properties.∧-isSemilattice
d_'8743''45'isSemilattice_3470 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8743''45'isSemilattice_3470
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_660
      (coe d_'8743''45'isBand_3466) erased
-- Data.Bool.Properties.∧-semilattice
d_'8743''45'semilattice_3472 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8743''45'semilattice_3472
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_84
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      d_'8743''45'isSemilattice_3470
-- Data.Bool.Properties.∧-isMonoid
d_'8743''45'isMonoid_3474 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8743''45'isMonoid_3474
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe d_'8743''45'isSemigroup_3462) (coe d_'8743''45'identity_3374)
-- Data.Bool.Properties.∧-isCommutativeMonoid
d_'8743''45'isCommutativeMonoid_3476 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'8743''45'isCommutativeMonoid_3476
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe d_'8743''45'isMonoid_3474) erased
-- Data.Bool.Properties.∧-commutativeMonoid
d_'8743''45'commutativeMonoid_3478 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'8743''45'commutativeMonoid_3478
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      d_'8743''45'isCommutativeMonoid_3476
-- Data.Bool.Properties.∧-isIdempotentCommutativeMonoid
d_'8743''45'isIdempotentCommutativeMonoid_3480 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'8743''45'isIdempotentCommutativeMonoid_3480
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_950
      (coe d_'8743''45'isCommutativeMonoid_3476) erased
-- Data.Bool.Properties.∧-idempotentCommutativeMonoid
d_'8743''45'idempotentCommutativeMonoid_3482 ::
  MAlonzo.Code.Algebra.Bundles.T_IdempotentCommutativeMonoid_1186
d_'8743''45'idempotentCommutativeMonoid_3482
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1296
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      d_'8743''45'isIdempotentCommutativeMonoid_3480
-- Data.Bool.Properties.∨-∧-isSemiring
d_'8744''45''8743''45'isSemiring_3484 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_'8744''45''8743''45'isSemiring_3484
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1740
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1630
         (coe d_'8744''45'isCommutativeMonoid_3350) erased erased
         (coe d_'8743''45'identity_3374)
         (coe d_'8743''45'distrib'45''8744'_3422))
      (coe d_'8743''45'zero_3380)
-- Data.Bool.Properties.∨-∧-isCommutativeSemiring
d_'8744''45''8743''45'isCommutativeSemiring_3486 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_'8744''45''8743''45'isCommutativeSemiring_3486
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe d_'8744''45''8743''45'isSemiring_3484) erased
-- Data.Bool.Properties.∨-∧-commutativeSemiring
d_'8744''45''8743''45'commutativeSemiring_3488 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
d_'8744''45''8743''45'commutativeSemiring_3488
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2706
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      d_'8744''45''8743''45'isCommutativeSemiring_3486
-- Data.Bool.Properties.∧-∨-isSemiring
d_'8743''45''8744''45'isSemiring_3490 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_'8743''45''8744''45'isSemiring_3490
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1740
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1630
         (coe d_'8743''45'isCommutativeMonoid_3476) erased erased
         (coe d_'8744''45'identity_3302)
         (coe d_'8744''45'distrib'45''8743'_3442))
      (coe d_'8744''45'zero_3308)
-- Data.Bool.Properties.∧-∨-isCommutativeSemiring
d_'8743''45''8744''45'isCommutativeSemiring_3492 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_'8743''45''8744''45'isCommutativeSemiring_3492
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe d_'8743''45''8744''45'isSemiring_3490) erased
-- Data.Bool.Properties.∧-∨-commutativeSemiring
d_'8743''45''8744''45'commutativeSemiring_3494 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
d_'8743''45''8744''45'commutativeSemiring_3494
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2706
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      d_'8743''45''8744''45'isCommutativeSemiring_3492
-- Data.Bool.Properties.∨-∧-isLattice
d_'8744''45''8743''45'isLattice_3496 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8744''45''8743''45'isLattice_3496
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3140
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased erased erased erased erased erased
      (coe d_'8744''45''8743''45'absorptive_3456)
-- Data.Bool.Properties.∨-∧-lattice
d_'8744''45''8743''45'lattice_3498 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8744''45''8743''45'lattice_3498
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_592
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      d_'8744''45''8743''45'isLattice_3496
-- Data.Bool.Properties.∨-∧-isDistributiveLattice
d_'8744''45''8743''45'isDistributiveLattice_3500 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_'8744''45''8743''45'isDistributiveLattice_3500
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3212
      (coe d_'8744''45''8743''45'isLattice_3496)
      (coe d_'8744''45'distrib'45''8743'_3442)
      (coe d_'8743''45'distrib'45''8744'_3422)
-- Data.Bool.Properties.∨-∧-distributiveLattice
d_'8744''45''8743''45'distributiveLattice_3502 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
d_'8744''45''8743''45'distributiveLattice_3502
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_692
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      d_'8744''45''8743''45'isDistributiveLattice_3500
-- Data.Bool.Properties.∨-∧-isBooleanAlgebra
d_'8744''45''8743''45'isBooleanAlgebra_3504 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224
d_'8744''45''8743''45'isBooleanAlgebra_3504
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3314
      (coe d_'8744''45''8743''45'isDistributiveLattice_3500)
      (coe d_'8744''45'inverse_3316) (coe d_'8743''45'inverse_3388)
      erased
-- Data.Bool.Properties.∨-∧-booleanAlgebra
d_'8744''45''8743''45'booleanAlgebra_3506 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_698
d_'8744''45''8743''45'booleanAlgebra_3506
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_822
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      MAlonzo.Code.Data.Bool.Base.d_not_22
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      d_'8744''45''8743''45'isBooleanAlgebra_3504
-- Data.Bool.Properties.not-involutive
d_not'45'involutive_3508 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'involutive_3508 = erased
-- Data.Bool.Properties.not-injective
d_not'45'injective_3514 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'injective_3514 = erased
-- Data.Bool.Properties.not-¬
d_not'45''172'_3524 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_not'45''172'_3524 = erased
-- Data.Bool.Properties.¬-not
d_'172''45'not_3530 ::
  Bool ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172''45'not_3530 = erased
-- Data.Bool.Properties.xor-is-ok
d_xor'45'is'45'ok_3540 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'is'45'ok_3540 = erased
-- Data.Bool.Properties.true-xor
d_true'45'xor_3548 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_true'45'xor_3548 = erased
-- Data.Bool.Properties.xor-same
d_xor'45'same_3552 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'same_3552 = erased
-- Data.Bool.Properties.not-distribˡ-xor
d_not'45'distrib'737''45'xor_3558 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'distrib'737''45'xor_3558 = erased
-- Data.Bool.Properties.not-distribʳ-xor
d_not'45'distrib'691''45'xor_3568 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'distrib'691''45'xor_3568 = erased
-- Data.Bool.Properties.xor-assoc
d_xor'45'assoc_3574 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'assoc_3574 = erased
-- Data.Bool.Properties.xor-comm
d_xor'45'comm_3584 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'comm_3584 = erased
-- Data.Bool.Properties.xor-identityˡ
d_xor'45'identity'737'_3586 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'identity'737'_3586 = erased
-- Data.Bool.Properties.xor-identityʳ
d_xor'45'identity'691'_3588 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'identity'691'_3588 = erased
-- Data.Bool.Properties.xor-identity
d_xor'45'identity_3590 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_xor'45'identity_3590
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.xor-inverseˡ
d_xor'45'inverse'737'_3592 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'inverse'737'_3592 = erased
-- Data.Bool.Properties.xor-inverseʳ
d_xor'45'inverse'691'_3594 ::
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'inverse'691'_3594 = erased
-- Data.Bool.Properties.xor-inverse
d_xor'45'inverse_3598 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_xor'45'inverse_3598
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.∧-distribˡ-xor
d_'8743''45'distrib'737''45'xor_3600 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'737''45'xor_3600 = erased
-- Data.Bool.Properties.∧-distribʳ-xor
d_'8743''45'distrib'691''45'xor_3610 ::
  Bool ->
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'691''45'xor_3610 = erased
-- Data.Bool.Properties.∧-distrib-xor
d_'8743''45'distrib'45'xor_3620 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45'xor_3620
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Bool.Properties.xor-annihilates-not
d_xor'45'annihilates'45'not_3626 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xor'45'annihilates'45'not_3626 = erased
-- Data.Bool.Properties.xor-∧-commutativeRing
d_xor'45''8743''45'commutativeRing_3632 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4126
d_xor'45''8743''45'commutativeRing_3632
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.BooleanAlgebra.du_'8853''45''8743''45'commutativeRing_3826
      (coe d_'8744''45''8743''45'booleanAlgebra_3506)
      (coe MAlonzo.Code.Data.Bool.Base.d__xor__36) erased
-- Data.Bool.Properties.if-float
d_if'45'float_3910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'float_3910 = erased
-- Data.Bool.Properties.if-eta
d_if'45'eta_3916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'eta_3916 = erased
-- Data.Bool.Properties.if-idem-then
d_if'45'idem'45'then_3924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'idem'45'then_3924 = erased
-- Data.Bool.Properties.if-idem-else
d_if'45'idem'45'else_3932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'idem'45'else_3932 = erased
-- Data.Bool.Properties.if-swap-then
d_if'45'swap'45'then_3942 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'swap'45'then_3942 = erased
-- Data.Bool.Properties.if-swap-else
d_if'45'swap'45'else_3952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'swap'45'else_3952 = erased
-- Data.Bool.Properties.if-not
d_if'45'not_3960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'not_3960 = erased
-- Data.Bool.Properties.if-∧
d_if'45''8743'_3970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45''8743'_3970 = erased
-- Data.Bool.Properties.if-∨
d_if'45''8744'_3980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45''8744'_3980 = erased
-- Data.Bool.Properties.if-xor
d_if'45'xor_3990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'xor_3990 = erased
-- Data.Bool.Properties.if-cong
d_if'45'cong_4000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  Bool ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'cong_4000 = erased
-- Data.Bool.Properties.if-cong-then
d_if'45'cong'45'then_4010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'cong'45'then_4010 = erased
-- Data.Bool.Properties.if-cong-else
d_if'45'cong'45'else_4020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'cong'45'else_4020 = erased
-- Data.Bool.Properties.if-cong₂
d_if'45'cong'8322'_4032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Bool ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_if'45'cong'8322'_4032 = erased
-- Data.Bool.Properties.T-≡
d_T'45''8801'_4036 ::
  Bool -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_T'45''8801'_4036 v0
  = if coe v0
      then coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 erased
             (let v1 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
              coe (coe (\ v2 -> v1)))
      else coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 erased erased
-- Data.Bool.Properties.T-not-≡
d_T'45'not'45''8801'_4040 ::
  Bool -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_T'45'not'45''8801'_4040 v0
  = if coe v0
      then coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 erased erased
      else coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 erased
             (let v1 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
              coe (coe (\ v2 -> v1)))
-- Data.Bool.Properties.T-∧
d_T'45''8743'_4046 ::
  Bool -> Bool -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_T'45''8743'_4046 v0 v1
  = if coe v0
      then if coe v1
             then coe
                    MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
                    (let v2
                           = coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                     coe (coe (\ v3 -> v2)))
                    (let v2 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
                     coe (coe (\ v3 -> v2)))
             else coe
                    MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 erased
                    (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
      else coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 erased
             (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
-- Data.Bool.Properties.T-∨
d_T'45''8744'_4052 ::
  Bool -> Bool -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_T'45''8744'_4052 v0 v1
  = if coe v0
      then coe
             MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
             (let v2 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
              coe (coe (\ v3 -> v2)))
      else (if coe v1
              then coe
                     MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                     (let v2 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
                      coe (coe (\ v3 -> v2)))
              else coe
                     MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                     (coe
                        MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52 (coe (\ v2 -> v2))
                        (coe (\ v2 -> v2))))
-- Data.Bool.Properties.T-irrelevant
d_T'45'irrelevant_4054 ::
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'45'irrelevant_4054 = erased
-- Data.Bool.Properties.T?-diag
d_T'63''45'diag_4058 :: Bool -> AgdaAny -> AgdaAny
d_T'63''45'diag_4058 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_fromWitness_150
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
         (coe v0)
         (coe
            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
            (coe v0)))
-- Data.Bool.Properties.⇔→≡
d_'8660''8594''8801'_4068 ::
  Bool ->
  Bool ->
  Bool ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8660''8594''8801'_4068 = erased
-- Data.Bool.Properties.push-function-into-if
d_push'45'function'45'into'45'if_4082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Bool ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45'function'45'into'45'if_4082 = erased
