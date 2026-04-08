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

module MAlonzo.Code.Data.Nat.Properties where

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
import qualified MAlonzo.Code.Algebra.Definitions.RawMagma
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Morphism
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Metric.Nat.Bundles
import qualified MAlonzo.Code.Function.Metric.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Binary.Structures.Biased
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Nat.Properties._._Absorbs_
d__Absorbs__8 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__Absorbs__8 = erased
-- Data.Nat.Properties._._DistributesOver_
d__DistributesOver__10 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver__10 = erased
-- Data.Nat.Properties._._DistributesOverʳ_
d__DistributesOver'691'__12 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver'691'__12 = erased
-- Data.Nat.Properties._._DistributesOverˡ_
d__DistributesOver'737'__14 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver'737'__14 = erased
-- Data.Nat.Properties._._IdempotentOn_
d__IdempotentOn__16 ::
  (Integer -> Integer -> Integer) -> Integer -> ()
d__IdempotentOn__16 = erased
-- Data.Nat.Properties._._MiddleFourExchange_
d__MiddleFourExchange__18 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__MiddleFourExchange__18 = erased
-- Data.Nat.Properties._.Absorptive
d_Absorptive_20 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_Absorptive_20 = erased
-- Data.Nat.Properties._.AlmostCancellative
d_AlmostCancellative_22 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_AlmostCancellative_22 = erased
-- Data.Nat.Properties._.AlmostLeftCancellative
d_AlmostLeftCancellative_24 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_AlmostLeftCancellative_24 = erased
-- Data.Nat.Properties._.AlmostRightCancellative
d_AlmostRightCancellative_26 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_AlmostRightCancellative_26 = erased
-- Data.Nat.Properties._.Alternative
d_Alternative_28 :: (Integer -> Integer -> Integer) -> ()
d_Alternative_28 = erased
-- Data.Nat.Properties._.Associative
d_Associative_30 :: (Integer -> Integer -> Integer) -> ()
d_Associative_30 = erased
-- Data.Nat.Properties._.Commutative
d_Commutative_32 :: (Integer -> Integer -> Integer) -> ()
d_Commutative_32 = erased
-- Data.Nat.Properties._.Congruent₁
d_Congruent'8321'_34 :: (Integer -> Integer) -> ()
d_Congruent'8321'_34 = erased
-- Data.Nat.Properties._.Congruent₂
d_Congruent'8322'_36 :: (Integer -> Integer -> Integer) -> ()
d_Congruent'8322'_36 = erased
-- Data.Nat.Properties._.Conical
d_Conical_38 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Conical_38 = erased
-- Data.Nat.Properties._.Flexible
d_Flexible_40 :: (Integer -> Integer -> Integer) -> ()
d_Flexible_40 = erased
-- Data.Nat.Properties._.Idempotent
d_Idempotent_42 :: (Integer -> Integer -> Integer) -> ()
d_Idempotent_42 = erased
-- Data.Nat.Properties._.IdempotentFun
d_IdempotentFun_44 :: (Integer -> Integer) -> ()
d_IdempotentFun_44 = erased
-- Data.Nat.Properties._.Identical
d_Identical_46 :: (Integer -> Integer -> Integer) -> ()
d_Identical_46 = erased
-- Data.Nat.Properties._.Identity
d_Identity_48 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Identity_48 = erased
-- Data.Nat.Properties._.Interchangable
d_Interchangable_50 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_Interchangable_50 = erased
-- Data.Nat.Properties._.Inverse
d_Inverse_52 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_Inverse_52 = erased
-- Data.Nat.Properties._.Invertible
d_Invertible_54 ::
  Integer -> (Integer -> Integer -> Integer) -> Integer -> ()
d_Invertible_54 = erased
-- Data.Nat.Properties._.Involutive
d_Involutive_56 :: (Integer -> Integer) -> ()
d_Involutive_56 = erased
-- Data.Nat.Properties._.LeftAlternative
d_LeftAlternative_58 :: (Integer -> Integer -> Integer) -> ()
d_LeftAlternative_58 = erased
-- Data.Nat.Properties._.LeftBol
d_LeftBol_60 :: (Integer -> Integer -> Integer) -> ()
d_LeftBol_60 = erased
-- Data.Nat.Properties._.LeftCongruent
d_LeftCongruent_62 :: (Integer -> Integer -> Integer) -> ()
d_LeftCongruent_62 = erased
-- Data.Nat.Properties._.LeftConical
d_LeftConical_64 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftConical_64 = erased
-- Data.Nat.Properties._.LeftDivides
d_LeftDivides_66 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_LeftDivides_66 = erased
-- Data.Nat.Properties._.LeftDividesʳ
d_LeftDivides'691'_68 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_LeftDivides'691'_68 = erased
-- Data.Nat.Properties._.LeftDividesˡ
d_LeftDivides'737'_70 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_LeftDivides'737'_70 = erased
-- Data.Nat.Properties._.LeftIdentity
d_LeftIdentity_72 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftIdentity_72 = erased
-- Data.Nat.Properties._.LeftInverse
d_LeftInverse_74 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_LeftInverse_74 = erased
-- Data.Nat.Properties._.LeftInvertible
d_LeftInvertible_76 ::
  Integer -> (Integer -> Integer -> Integer) -> Integer -> ()
d_LeftInvertible_76 = erased
-- Data.Nat.Properties._.LeftSemimedial
d_LeftSemimedial_78 :: (Integer -> Integer -> Integer) -> ()
d_LeftSemimedial_78 = erased
-- Data.Nat.Properties._.LeftZero
d_LeftZero_80 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftZero_80 = erased
-- Data.Nat.Properties._.Medial
d_Medial_82 :: (Integer -> Integer -> Integer) -> ()
d_Medial_82 = erased
-- Data.Nat.Properties._.MiddleBol
d_MiddleBol_84 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_MiddleBol_84 = erased
-- Data.Nat.Properties._.RightAlternative
d_RightAlternative_86 :: (Integer -> Integer -> Integer) -> ()
d_RightAlternative_86 = erased
-- Data.Nat.Properties._.RightBol
d_RightBol_88 :: (Integer -> Integer -> Integer) -> ()
d_RightBol_88 = erased
-- Data.Nat.Properties._.RightCongruent
d_RightCongruent_90 :: (Integer -> Integer -> Integer) -> ()
d_RightCongruent_90 = erased
-- Data.Nat.Properties._.RightConical
d_RightConical_92 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_RightConical_92 = erased
-- Data.Nat.Properties._.RightDivides
d_RightDivides_94 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_RightDivides_94 = erased
-- Data.Nat.Properties._.RightDividesʳ
d_RightDivides'691'_96 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_RightDivides'691'_96 = erased
-- Data.Nat.Properties._.RightDividesˡ
d_RightDivides'737'_98 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d_RightDivides'737'_98 = erased
-- Data.Nat.Properties._.RightIdentity
d_RightIdentity_100 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_RightIdentity_100 = erased
-- Data.Nat.Properties._.RightInverse
d_RightInverse_102 ::
  Integer ->
  (Integer -> Integer) -> (Integer -> Integer -> Integer) -> ()
d_RightInverse_102 = erased
-- Data.Nat.Properties._.RightInvertible
d_RightInvertible_104 ::
  Integer -> (Integer -> Integer -> Integer) -> Integer -> ()
d_RightInvertible_104 = erased
-- Data.Nat.Properties._.RightSemimedial
d_RightSemimedial_106 :: (Integer -> Integer -> Integer) -> ()
d_RightSemimedial_106 = erased
-- Data.Nat.Properties._.RightZero
d_RightZero_108 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_RightZero_108 = erased
-- Data.Nat.Properties._.Selective
d_Selective_110 :: (Integer -> Integer -> Integer) -> ()
d_Selective_110 = erased
-- Data.Nat.Properties._.SelfInverse
d_SelfInverse_112 :: (Integer -> Integer) -> ()
d_SelfInverse_112 = erased
-- Data.Nat.Properties._.Semimedial
d_Semimedial_114 :: (Integer -> Integer -> Integer) -> ()
d_Semimedial_114 = erased
-- Data.Nat.Properties._.StarDestructive
d_StarDestructive_116 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarDestructive_116 = erased
-- Data.Nat.Properties._.StarExpansive
d_StarExpansive_118 ::
  Integer ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarExpansive_118 = erased
-- Data.Nat.Properties._.StarLeftDestructive
d_StarLeftDestructive_120 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarLeftDestructive_120 = erased
-- Data.Nat.Properties._.StarLeftExpansive
d_StarLeftExpansive_122 ::
  Integer ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarLeftExpansive_122 = erased
-- Data.Nat.Properties._.StarRightDestructive
d_StarRightDestructive_124 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarRightDestructive_124 = erased
-- Data.Nat.Properties._.StarRightExpansive
d_StarRightExpansive_126 ::
  Integer ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> (Integer -> Integer) -> ()
d_StarRightExpansive_126 = erased
-- Data.Nat.Properties._.Zero
d_Zero_128 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Zero_128 = erased
-- Data.Nat.Properties._.IsAbelianGroup
d_IsAbelianGroup_132 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsAlternativeMagma
d_IsAlternativeMagma_136 a0 = ()
-- Data.Nat.Properties._.IsBand
d_IsBand_140 a0 = ()
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_144 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsCommutativeBand
d_IsCommutativeBand_148 a0 = ()
-- Data.Nat.Properties._.IsCommutativeMagma
d_IsCommutativeMagma_152 a0 = ()
-- Data.Nat.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_156 a0 a1 = ()
-- Data.Nat.Properties._.IsCommutativeRing
d_IsCommutativeRing_160 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_164 a0 = ()
-- Data.Nat.Properties._.IsCommutativeSemiring
d_IsCommutativeSemiring_168 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_172 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsFlexibleMagma
d_IsFlexibleMagma_176 a0 = ()
-- Data.Nat.Properties._.IsGroup
d_IsGroup_180 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_184 a0 a1 = ()
-- Data.Nat.Properties._.IsIdempotentMagma
d_IsIdempotentMagma_188 a0 = ()
-- Data.Nat.Properties._.IsIdempotentMonoid
d_IsIdempotentMonoid_192 a0 a1 = ()
-- Data.Nat.Properties._.IsIdempotentSemiring
d_IsIdempotentSemiring_196 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsInvertibleMagma
d_IsInvertibleMagma_200 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_204 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsKleeneAlgebra
d_IsKleeneAlgebra_208 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsLeftBolLoop
d_IsLeftBolLoop_212 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsLoop
d_IsLoop_216 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsMagma
d_IsMagma_220 a0 = ()
-- Data.Nat.Properties._.IsMedialMagma
d_IsMedialMagma_224 a0 = ()
-- Data.Nat.Properties._.IsMiddleBolLoop
d_IsMiddleBolLoop_228 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsMonoid
d_IsMonoid_232 a0 a1 = ()
-- Data.Nat.Properties._.IsMoufangLoop
d_IsMoufangLoop_236 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsNearSemiring
d_IsNearSemiring_240 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsNearring
d_IsNearring_244 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsNonAssociativeRing
d_IsNonAssociativeRing_248 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsQuasigroup
d_IsQuasigroup_252 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsQuasiring
d_IsQuasiring_256 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsRightBolLoop
d_IsRightBolLoop_260 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsRing
d_IsRing_264 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsRingWithoutOne
d_IsRingWithoutOne_268 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsSelectiveMagma
d_IsSelectiveMagma_272 a0 = ()
-- Data.Nat.Properties._.IsSemigroup
d_IsSemigroup_276 a0 = ()
-- Data.Nat.Properties._.IsSemimedialMagma
d_IsSemimedialMagma_280 a0 = ()
-- Data.Nat.Properties._.IsSemiring
d_IsSemiring_284 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_288 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsSemiringWithoutOne
d_IsSemiringWithoutOne_292 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsSuccessorSet
d_IsSuccessorSet_296 a0 a1 = ()
-- Data.Nat.Properties._.IsUnitalMagma
d_IsUnitalMagma_300 a0 a1 = ()
-- Data.Nat.Properties._.IsAbelianGroup._//_
d__'47''47'__306 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> Integer -> Integer
d__'47''47'__306 v0 ~v1 v2 ~v3 = du__'47''47'__306 v0 v2
du__'47''47'__306 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__306 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Nat.Properties._.IsAbelianGroup.assoc
d_assoc_308 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_308 = erased
-- Data.Nat.Properties._.IsAbelianGroup.comm
d_comm_310 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_310 = erased
-- Data.Nat.Properties._.IsAbelianGroup.identity
d_identity_312 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_312 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))
-- Data.Nat.Properties._.IsAbelianGroup.identityʳ
d_identity'691'_314 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_314 = erased
-- Data.Nat.Properties._.IsAbelianGroup.identityˡ
d_identity'737'_316 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_316 = erased
-- Data.Nat.Properties._.IsAbelianGroup.inverse
d_inverse_318 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_318 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Nat.Properties._.IsAbelianGroup.inverseʳ
d_inverse'691'_320 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_320 = erased
-- Data.Nat.Properties._.IsAbelianGroup.inverseˡ
d_inverse'737'_322 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_322 = erased
-- Data.Nat.Properties._.IsAbelianGroup.isCommutativeMagma
d_isCommutativeMagma_324 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_324 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_324 v3
du_isCommutativeMagma_324 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_324 v0
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
-- Data.Nat.Properties._.IsAbelianGroup.isCommutativeMonoid
d_isCommutativeMonoid_326 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_326 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244 v3
-- Data.Nat.Properties._.IsAbelianGroup.isCommutativeSemigroup
d_isCommutativeSemigroup_328 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_328 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_328 v3
du_isCommutativeSemigroup_328 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_328 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
         (coe v0))
-- Data.Nat.Properties._.IsAbelianGroup.isEquivalence
d_isEquivalence_330 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_330 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))))
-- Data.Nat.Properties._.IsAbelianGroup.isGroup
d_isGroup_332 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_332 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)
-- Data.Nat.Properties._.IsAbelianGroup.isInvertibleMagma
d_isInvertibleMagma_334 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_334 ~v0 ~v1 ~v2 v3
  = du_isInvertibleMagma_334 v3
du_isInvertibleMagma_334 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_334 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Nat.Properties._.IsAbelianGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_336 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_336 ~v0 ~v1 ~v2 v3
  = du_isInvertibleUnitalMagma_336 v3
du_isInvertibleUnitalMagma_336 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_336 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Nat.Properties._.IsAbelianGroup.isMagma
d_isMagma_338 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_338 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))))
-- Data.Nat.Properties._.IsAbelianGroup.isMonoid
d_isMonoid_340 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_340 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Nat.Properties._.IsAbelianGroup.isPartialEquivalence
d_isPartialEquivalence_342 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_342 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_342 v3
du_isPartialEquivalence_342 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_342 v0
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
-- Data.Nat.Properties._.IsAbelianGroup.isSemigroup
d_isSemigroup_344 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_344 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))
-- Data.Nat.Properties._.IsAbelianGroup.isUnitalMagma
d_isUnitalMagma_346 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_346 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_346 v3
du_isUnitalMagma_346 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_346 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1)))
-- Data.Nat.Properties._.IsAbelianGroup.refl
d_refl_348 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_348 = erased
-- Data.Nat.Properties._.IsAbelianGroup.reflexive
d_reflexive_350 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_350 = erased
-- Data.Nat.Properties._.IsAbelianGroup.setoid
d_setoid_352 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_352 ~v0 ~v1 ~v2 v3 = du_setoid_352 v3
du_setoid_352 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_352 v0
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
-- Data.Nat.Properties._.IsAbelianGroup.sym
d_sym_354 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_354 = erased
-- Data.Nat.Properties._.IsAbelianGroup.trans
d_trans_356 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_356 = erased
-- Data.Nat.Properties._.IsAbelianGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_358 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_358 = erased
-- Data.Nat.Properties._.IsAbelianGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_360 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_360 = erased
-- Data.Nat.Properties._.IsAbelianGroup.⁻¹-cong
d_'8315''185''45'cong_362 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_362 = erased
-- Data.Nat.Properties._.IsAbelianGroup.∙-cong
d_'8729''45'cong_364 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_364 = erased
-- Data.Nat.Properties._.IsAbelianGroup.∙-congʳ
d_'8729''45'cong'691'_366 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_366 = erased
-- Data.Nat.Properties._.IsAbelianGroup.∙-congˡ
d_'8729''45'cong'737'_368 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_368 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.alter
d_alter_372 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_372 v0
  = coe MAlonzo.Code.Algebra.Structures.d_alter_300 (coe v0)
-- Data.Nat.Properties._.IsAlternativeMagma.alternativeʳ
d_alternative'691'_374 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'691'_374 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.alternativeˡ
d_alternative'737'_376 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'737'_376 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.isEquivalence
d_isEquivalence_378 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_378 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0))
-- Data.Nat.Properties._.IsAlternativeMagma.isMagma
d_isMagma_380 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_380 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0)
-- Data.Nat.Properties._.IsAlternativeMagma.isPartialEquivalence
d_isPartialEquivalence_382 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_382 ~v0 v1 = du_isPartialEquivalence_382 v1
du_isPartialEquivalence_382 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_382 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsAlternativeMagma.refl
d_refl_384 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_384 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.reflexive
d_reflexive_386 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_386 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.setoid
d_setoid_388 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_388 ~v0 v1 = du_setoid_388 v1
du_setoid_388 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_388 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0))
-- Data.Nat.Properties._.IsAlternativeMagma.sym
d_sym_390 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_390 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.trans
d_trans_392 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_392 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.∙-cong
d_'8729''45'cong_394 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_394 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.∙-congʳ
d_'8729''45'cong'691'_396 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_396 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.∙-congˡ
d_'8729''45'cong'737'_398 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_398 = erased
-- Data.Nat.Properties._.IsBand.assoc
d_assoc_402 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_402 = erased
-- Data.Nat.Properties._.IsBand.idem
d_idem_404 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_404 = erased
-- Data.Nat.Properties._.IsBand.isEquivalence
d_isEquivalence_406 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_406 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)))
-- Data.Nat.Properties._.IsBand.isMagma
d_isMagma_408 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_408 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0))
-- Data.Nat.Properties._.IsBand.isPartialEquivalence
d_isPartialEquivalence_410 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_410 ~v0 v1 = du_isPartialEquivalence_410 v1
du_isPartialEquivalence_410 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_410 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Nat.Properties._.IsBand.isSemigroup
d_isSemigroup_412 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_412 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)
-- Data.Nat.Properties._.IsBand.refl
d_refl_414 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_414 = erased
-- Data.Nat.Properties._.IsBand.reflexive
d_reflexive_416 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_416 = erased
-- Data.Nat.Properties._.IsBand.setoid
d_setoid_418 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_418 ~v0 v1 = du_setoid_418 v1
du_setoid_418 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_418 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Nat.Properties._.IsBand.sym
d_sym_420 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_420 = erased
-- Data.Nat.Properties._.IsBand.trans
d_trans_422 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_422 = erased
-- Data.Nat.Properties._.IsBand.∙-cong
d_'8729''45'cong_424 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_424 = erased
-- Data.Nat.Properties._.IsBand.∙-congʳ
d_'8729''45'cong'691'_426 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_426 = erased
-- Data.Nat.Properties._.IsBand.∙-congˡ
d_'8729''45'cong'737'_428 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_428 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-assoc
d_'42''45'assoc_432 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_432 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-cancelʳ-nonZero
d_'42''45'cancel'691''45'nonZero_434 ::
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
d_'42''45'cancel'691''45'nonZero_434 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_436 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45'nonZero_436 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-comm
d_'42''45'comm_438 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_438 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-cong
d_'42''45'cong_440 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_440 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_442 ::
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
d_'8729''45'cong'691'_442 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_444 ::
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
d_'8729''45'cong'737'_444 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-identity
d_'42''45'identity_446 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_446 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.identityʳ
d_identity'691'_448 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_448 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.identityˡ
d_identity'737'_450 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_450 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_452 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_452 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_452 v4
du_isCommutativeMagma_452 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_452 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_454 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_454 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeMonoid_454 v4
du_'42''45'isCommutativeMonoid_454 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_454 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_456 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_456 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeSemigroup_456 v4
du_'42''45'isCommutativeSemigroup_456 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_456 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
            (coe v1)))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-isMagma
d_'42''45'isMagma_458 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_458 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_458 v4
du_'42''45'isMagma_458 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_458 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-isMonoid
d_'42''45'isMonoid_460 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_460 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_460 v4
du_'42''45'isMonoid_460 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_460 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-isSemigroup
d_'42''45'isSemigroup_462 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_462 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_462 v4
du_'42''45'isSemigroup_462 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_462 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.assoc
d_assoc_464 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_464 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.comm
d_comm_466 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_466 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.∙-cong
d_'8729''45'cong_468 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_468 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_470 ::
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
d_'8729''45'cong'691'_470 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_472 ::
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
d_'8729''45'cong'737'_472 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.identity
d_identity_474 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_474 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.identityʳ
d_identity'691'_476 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_476 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.identityˡ
d_identity'737'_478 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_478 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_480 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_480 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_480 v4
du_isCommutativeMagma_480 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_480 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_482 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_482 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_484 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_484 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_484 v4
du_isCommutativeSemigroup_484 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_484 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isMagma
d_isMagma_486 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_486 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isMonoid
d_isMonoid_488 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_488 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isSemigroup
d_isSemigroup_490 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_490 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isUnitalMagma
d_isUnitalMagma_492 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_492 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_492 v4
du_isUnitalMagma_492 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_492 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.distrib
d_distrib_494 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_494 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.distribʳ
d_distrib'691'_496 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_496 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.distribˡ
d_distrib'737'_498 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_498 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_500 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_500 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
      (coe v0)
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_502 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_502 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemiringWithoutOne_502 v4
du_isCommutativeSemiringWithoutOne_502 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_502 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isEquivalence
d_isEquivalence_504 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_504 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isNearSemiring
d_isNearSemiring_506 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_506 ~v0 ~v1 ~v2 ~v3 v4 = du_isNearSemiring_506 v4
du_isNearSemiring_506 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_506 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isPartialEquivalence
d_isPartialEquivalence_508 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_508 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_508 v4
du_isPartialEquivalence_508 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_508 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isSemiring
d_isSemiring_510 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_510 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_512 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_512 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
            (coe v0)))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_514 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_514 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_514 v4
du_isSemiringWithoutOne_514 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_514 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1)))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.refl
d_refl_516 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_516 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.reflexive
d_reflexive_518 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_518 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.setoid
d_setoid_520 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_520 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_520 v4
du_setoid_520 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_520 v0
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
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.sym
d_sym_522 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_522 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.trans
d_trans_524 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_524 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.zero
d_zero_526 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_526 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
            (coe v0)))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.zeroʳ
d_zero'691'_528 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_528 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.zeroˡ
d_zero'737'_530 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_530 = erased
-- Data.Nat.Properties._.IsCommutativeBand.assoc
d_assoc_534 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_534 = erased
-- Data.Nat.Properties._.IsCommutativeBand.comm
d_comm_536 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_536 = erased
-- Data.Nat.Properties._.IsCommutativeBand.idem
d_idem_538 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_538 = erased
-- Data.Nat.Properties._.IsCommutativeBand.isBand
d_isBand_540 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_540 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Data.Nat.Properties._.IsCommutativeBand.isCommutativeMagma
d_isCommutativeMagma_542 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_542 ~v0 v1 = du_isCommutativeMagma_542 v1
du_isCommutativeMagma_542 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_654
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeBand.isCommutativeSemigroup
d_isCommutativeSemigroup_544 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_544 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_654 v1
-- Data.Nat.Properties._.IsCommutativeBand.isEquivalence
d_isEquivalence_546 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_546 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Data.Nat.Properties._.IsCommutativeBand.isMagma
d_isMagma_548 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_548 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeBand.isPartialEquivalence
d_isPartialEquivalence_550 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_550 ~v0 v1 = du_isPartialEquivalence_550 v1
du_isPartialEquivalence_550 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_550 v0
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
-- Data.Nat.Properties._.IsCommutativeBand.isSemigroup
d_isSemigroup_552 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_552 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Data.Nat.Properties._.IsCommutativeBand.refl
d_refl_554 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_554 = erased
-- Data.Nat.Properties._.IsCommutativeBand.reflexive
d_reflexive_556 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_556 = erased
-- Data.Nat.Properties._.IsCommutativeBand.setoid
d_setoid_558 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_558 ~v0 v1 = du_setoid_558 v1
du_setoid_558 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_558 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Nat.Properties._.IsCommutativeBand.sym
d_sym_560 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_560 = erased
-- Data.Nat.Properties._.IsCommutativeBand.trans
d_trans_562 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_562 = erased
-- Data.Nat.Properties._.IsCommutativeBand.∙-cong
d_'8729''45'cong_564 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_564 = erased
-- Data.Nat.Properties._.IsCommutativeBand.∙-congʳ
d_'8729''45'cong'691'_566 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_566 = erased
-- Data.Nat.Properties._.IsCommutativeBand.∙-congˡ
d_'8729''45'cong'737'_568 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_568 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.comm
d_comm_572 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_572 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.isEquivalence
d_isEquivalence_574 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_574 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0))
-- Data.Nat.Properties._.IsCommutativeMagma.isMagma
d_isMagma_576 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_576 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0)
-- Data.Nat.Properties._.IsCommutativeMagma.isPartialEquivalence
d_isPartialEquivalence_578 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_578 ~v0 v1 = du_isPartialEquivalence_578 v1
du_isPartialEquivalence_578 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_578 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsCommutativeMagma.refl
d_refl_580 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_580 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.reflexive
d_reflexive_582 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_582 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.setoid
d_setoid_584 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_584 ~v0 v1 = du_setoid_584 v1
du_setoid_584 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_584 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0))
-- Data.Nat.Properties._.IsCommutativeMagma.sym
d_sym_586 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_586 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.trans
d_trans_588 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_588 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.∙-cong
d_'8729''45'cong_590 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_590 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.∙-congʳ
d_'8729''45'cong'691'_592 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_592 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.∙-congˡ
d_'8729''45'cong'737'_594 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_594 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.assoc
d_assoc_598 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_598 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.comm
d_comm_600 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_600 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.identity
d_identity_602 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_602 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Nat.Properties._.IsCommutativeMonoid.identityʳ
d_identity'691'_604 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_604 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.identityˡ
d_identity'737'_606 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_606 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_608 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_608 ~v0 ~v1 v2 = du_isCommutativeMagma_608 v2
du_isCommutativeMagma_608 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_608 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_610 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_610 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814 v2
-- Data.Nat.Properties._.IsCommutativeMonoid.isEquivalence
d_isEquivalence_612 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_612 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))))
-- Data.Nat.Properties._.IsCommutativeMonoid.isMagma
d_isMagma_614 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_614 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_616 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_616 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)
-- Data.Nat.Properties._.IsCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_618 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_618 ~v0 ~v1 v2
  = du_isPartialEquivalence_618 v2
du_isPartialEquivalence_618 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_618 v0
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
-- Data.Nat.Properties._.IsCommutativeMonoid.isSemigroup
d_isSemigroup_620 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_620 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Nat.Properties._.IsCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_622 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_622 ~v0 ~v1 v2 = du_isUnitalMagma_622 v2
du_isUnitalMagma_622 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_622 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Nat.Properties._.IsCommutativeMonoid.refl
d_refl_624 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_624 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.reflexive
d_reflexive_626 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_626 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.setoid
d_setoid_628 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_628 ~v0 ~v1 v2 = du_setoid_628 v2
du_setoid_628 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_628 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Nat.Properties._.IsCommutativeMonoid.sym
d_sym_630 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_630 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.trans
d_trans_632 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_632 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.∙-cong
d_'8729''45'cong_634 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_634 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_636 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_636 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_638 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_638 = erased
-- Data.Nat.Properties._.IsCommutativeRing._//_
d__'47''47'__642 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> Integer -> Integer
d__'47''47'__642 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__642 v0 v2
du__'47''47'__642 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__642 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Nat.Properties._.IsCommutativeRing.*-assoc
d_'42''45'assoc_644 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_644 = erased
-- Data.Nat.Properties._.IsCommutativeRing.*-comm
d_'42''45'comm_646 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_646 = erased
-- Data.Nat.Properties._.IsCommutativeRing.*-cong
d_'42''45'cong_648 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_648 = erased
-- Data.Nat.Properties._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_650 ::
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
d_'8729''45'cong'691'_650 = erased
-- Data.Nat.Properties._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_652 ::
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
d_'8729''45'cong'737'_652 = erased
-- Data.Nat.Properties._.IsCommutativeRing.*-identity
d_'42''45'identity_654 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_654 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Nat.Properties._.IsCommutativeRing.identityʳ
d_identity'691'_656 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_656 = erased
-- Data.Nat.Properties._.IsCommutativeRing.identityˡ
d_identity'737'_658 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_658 = erased
-- Data.Nat.Properties._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_660 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_660 v0 v1 v2 v3 ~v4 v5
  = du_isCommutativeMagma_660 v0 v1 v2 v3 v5
du_isCommutativeMagma_660 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_660 v0 v1 v2 v3 v4
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
-- Data.Nat.Properties._.IsCommutativeRing.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_662 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_662 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isCommutativeMonoid_662 v0 v1 v2 v3 v5
du_'42''45'isCommutativeMonoid_662 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_662 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Nat.Properties._.IsCommutativeRing.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_664 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_664 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isCommutativeSemigroup_664 v0 v1 v2 v3 v5
du_'42''45'isCommutativeSemigroup_664 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_664 v0 v1 v2 v3 v4
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
-- Data.Nat.Properties._.IsCommutativeRing.*-isMagma
d_'42''45'isMagma_666 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_666 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMagma_666 v0 v1 v2 v3 v5
du_'42''45'isMagma_666 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_666 v0 v1 v2 v3 v4
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
-- Data.Nat.Properties._.IsCommutativeRing.*-isMonoid
d_'42''45'isMonoid_668 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_668 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMonoid_668 v0 v1 v2 v3 v5
du_'42''45'isMonoid_668 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_668 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2860 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4))
-- Data.Nat.Properties._.IsCommutativeRing.*-isSemigroup
d_'42''45'isSemigroup_670 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_670 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isSemigroup_670 v0 v1 v2 v3 v5
du_'42''45'isSemigroup_670 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_670 v0 v1 v2 v3 v4
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
-- Data.Nat.Properties._.IsCommutativeRing.assoc
d_assoc_672 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_672 = erased
-- Data.Nat.Properties._.IsCommutativeRing.comm
d_comm_674 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_674 = erased
-- Data.Nat.Properties._.IsCommutativeRing.∙-cong
d_'8729''45'cong_676 ::
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
d_'8729''45'cong_676 = erased
-- Data.Nat.Properties._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_678 ::
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
d_'8729''45'cong'691'_678 = erased
-- Data.Nat.Properties._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_680 ::
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
d_'8729''45'cong'737'_680 = erased
-- Data.Nat.Properties._.IsCommutativeRing.identity
d_identity_682 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_682 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_682 v5
du_identity_682 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_682 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.identityʳ
d_identity'691'_684 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_684 = erased
-- Data.Nat.Properties._.IsCommutativeRing.identityˡ
d_identity'737'_686 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_686 = erased
-- Data.Nat.Properties._.IsCommutativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_688 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_688 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Nat.Properties._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_690 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_690 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_690 v5
du_isCommutativeMagma_690 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_690 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isCommutativeMonoid
d_isCommutativeMonoid_692 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_692 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_692 v5
du_isCommutativeMonoid_692 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_692 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_694 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_694 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_694 v5
du_isCommutativeSemigroup_694 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_694 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isGroup
d_isGroup_696 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_696 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_696 v5
du_isGroup_696 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
du_isGroup_696 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v1)))
-- Data.Nat.Properties._.IsCommutativeRing.isInvertibleMagma
d_isInvertibleMagma_698 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_698 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_698 v5
du_isInvertibleMagma_698 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_698 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_700 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_700 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_700 v5
du_isInvertibleUnitalMagma_700 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_700 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isMagma
d_isMagma_702 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_702 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_702 v5
du_isMagma_702 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_702 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isMonoid
d_isMonoid_704 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_704 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_704 v5
du_isMonoid_704 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_isMonoid_704 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isSemigroup
d_isSemigroup_706 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_706 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_706 v5
du_isSemigroup_706 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_706 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isUnitalMagma
d_isUnitalMagma_708 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_708 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_708 v5
du_isUnitalMagma_708 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_708 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.⁻¹-cong
d_'8315''185''45'cong_710 ::
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
d_'8315''185''45'cong_710 = erased
-- Data.Nat.Properties._.IsCommutativeRing.inverse
d_inverse_712 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_712 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_712 v5
du_inverse_712 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_712 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.inverseʳ
d_inverse'691'_714 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_714 = erased
-- Data.Nat.Properties._.IsCommutativeRing.inverseˡ
d_inverse'737'_716 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_716 = erased
-- Data.Nat.Properties._.IsCommutativeRing.distrib
d_distrib_718 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_718 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2770
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Nat.Properties._.IsCommutativeRing.distribʳ
d_distrib'691'_720 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_720 = erased
-- Data.Nat.Properties._.IsCommutativeRing.distribˡ
d_distrib'737'_722 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_722 = erased
-- Data.Nat.Properties._.IsCommutativeRing.isCommutativeSemiring
d_isCommutativeSemiring_724 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_724 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018 v0 v1
      v2 v3 v5
-- Data.Nat.Properties._.IsCommutativeRing.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_726 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_726 v0 v1 v2 v3 ~v4 v5
  = du_isCommutativeSemiringWithoutOne_726 v0 v1 v2 v3 v5
du_isCommutativeSemiringWithoutOne_726 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_726 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Nat.Properties._.IsCommutativeRing.isEquivalence
d_isEquivalence_728 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_728 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_728 v5
du_isEquivalence_728 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_728 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isNearSemiring
d_isNearSemiring_730 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_730 v0 v1 v2 v3 ~v4 v5
  = du_isNearSemiring_730 v0 v1 v2 v3 v5
du_isNearSemiring_730 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_730 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v5)))
-- Data.Nat.Properties._.IsCommutativeRing.isPartialEquivalence
d_isPartialEquivalence_732 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_732 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_732 v5
du_isPartialEquivalence_732 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_732 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.isRing
d_isRing_734 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_isRing_734 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0)
-- Data.Nat.Properties._.IsCommutativeRing.isRingWithoutOne
d_isRingWithoutOne_736 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
d_isRingWithoutOne_736 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isRingWithoutOne_736 v5
du_isRingWithoutOne_736 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
du_isRingWithoutOne_736 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Nat.Properties._.IsCommutativeRing.isSemiring
d_isSemiring_738 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_738 v0 v1 v2 v3 ~v4 v5
  = du_isSemiring_738 v0 v1 v2 v3 v5
du_isSemiring_738 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
du_isSemiring_738 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4))
-- Data.Nat.Properties._.IsCommutativeRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_740 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_740 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isSemiringWithoutAnnihilatingZero_740 v5
du_isSemiringWithoutAnnihilatingZero_740 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
du_isSemiringWithoutAnnihilatingZero_740 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2868
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Nat.Properties._.IsCommutativeRing.isSemiringWithoutOne
d_isSemiringWithoutOne_742 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_742 v0 v1 v2 v3 ~v4 v5
  = du_isSemiringWithoutOne_742 v0 v1 v2 v3 v5
du_isSemiringWithoutOne_742 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_742 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Data.Nat.Properties._.IsCommutativeRing.refl
d_refl_744 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_744 = erased
-- Data.Nat.Properties._.IsCommutativeRing.reflexive
d_reflexive_746 ::
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
d_reflexive_746 = erased
-- Data.Nat.Properties._.IsCommutativeRing.setoid
d_setoid_748 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_748 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_748 v5
du_setoid_748 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_748 v0
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
-- Data.Nat.Properties._.IsCommutativeRing.sym
d_sym_750 ::
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
d_sym_750 = erased
-- Data.Nat.Properties._.IsCommutativeRing.trans
d_trans_752 ::
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
d_trans_752 = erased
-- Data.Nat.Properties._.IsCommutativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_754 ::
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
d_unique'691''45''8315''185'_754 = erased
-- Data.Nat.Properties._.IsCommutativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_756 ::
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
d_unique'737''45''8315''185'_756 = erased
-- Data.Nat.Properties._.IsCommutativeRing.zero
d_zero_758 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_758 v0 v1 v2 v3 ~v4 v5 = du_zero_758 v0 v1 v2 v3 v5
du_zero_758 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_758 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero_2468 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v5)))
-- Data.Nat.Properties._.IsCommutativeRing.zeroʳ
d_zero'691'_760 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_760 = erased
-- Data.Nat.Properties._.IsCommutativeRing.zeroˡ
d_zero'737'_762 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_762 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.assoc
d_assoc_766 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_766 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.comm
d_comm_768 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_768 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.isCommutativeMagma
d_isCommutativeMagma_770 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_770 v0 v1
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606 v1
-- Data.Nat.Properties._.IsCommutativeSemigroup.isEquivalence
d_isEquivalence_772 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_772 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemigroup.isMagma
d_isMagma_774 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_774 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemigroup.isPartialEquivalence
d_isPartialEquivalence_776 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_776 ~v0 v1 = du_isPartialEquivalence_776 v1
du_isPartialEquivalence_776 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_776 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Nat.Properties._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_778 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_778 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)
-- Data.Nat.Properties._.IsCommutativeSemigroup.refl
d_refl_780 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_780 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.reflexive
d_reflexive_782 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_782 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.setoid
d_setoid_784 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_784 ~v0 v1 = du_setoid_784 v1
du_setoid_784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_784 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Nat.Properties._.IsCommutativeSemigroup.sym
d_sym_786 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_786 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.trans
d_trans_788 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_788 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.∙-cong
d_'8729''45'cong_790 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_790 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.∙-congʳ
d_'8729''45'cong'691'_792 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_792 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.∙-congˡ
d_'8729''45'cong'737'_794 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_794 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.*-assoc
d_'42''45'assoc_798 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_798 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.*-comm
d_'42''45'comm_800 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_800 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.*-cong
d_'42''45'cong_802 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_802 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_804 ::
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
d_'8729''45'cong'691'_804 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_806 ::
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
d_'8729''45'cong'737'_806 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.*-identity
d_'42''45'identity_808 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_808 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemiring.identityʳ
d_identity'691'_810 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_810 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.identityˡ
d_identity'737'_812 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_812 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_814 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_814 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_814 v4
du_isCommutativeMagma_814 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_814 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_816 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_816 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      v4
-- Data.Nat.Properties._.IsCommutativeSemiring.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_818 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_818 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeSemigroup_818 v4
du_'42''45'isCommutativeSemigroup_818 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_818 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiring.*-isMagma
d_'42''45'isMagma_820 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_820 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_820 v4
du_'42''45'isMagma_820 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_820 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Nat.Properties._.IsCommutativeSemiring.*-isMonoid
d_'42''45'isMonoid_822 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_822 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_822 v4
du_'42''45'isMonoid_822 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_822 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Nat.Properties._.IsCommutativeSemiring.*-isSemigroup
d_'42''45'isSemigroup_824 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_824 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_824 v4
du_'42''45'isSemigroup_824 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_824 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Nat.Properties._.IsCommutativeSemiring.assoc
d_assoc_826 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_826 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.comm
d_comm_828 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_828 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.∙-cong
d_'8729''45'cong_830 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_830 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_832 ::
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
d_'8729''45'cong'691'_832 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_834 ::
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
d_'8729''45'cong'737'_834 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.identity
d_identity_836 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_836 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))))
-- Data.Nat.Properties._.IsCommutativeSemiring.identityʳ
d_identity'691'_838 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_838 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.identityˡ
d_identity'737'_840 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_840 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_842 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_842 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_842 v4
du_isCommutativeMagma_842 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_842 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_844 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_844 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_846 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_846 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_846 v4
du_isCommutativeSemigroup_846 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_846 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiring.isMagma
d_isMagma_848 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_848 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiring.isMonoid
d_isMonoid_850 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_850 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))))
-- Data.Nat.Properties._.IsCommutativeSemiring.isSemigroup
d_isSemigroup_852 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_852 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))))
-- Data.Nat.Properties._.IsCommutativeSemiring.isUnitalMagma
d_isUnitalMagma_854 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_854 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_854 v4
du_isUnitalMagma_854 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_854 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiring.distrib
d_distrib_856 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_856 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemiring.distribʳ
d_distrib'691'_858 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_858 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.distribˡ
d_distrib'737'_860 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_860 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_862 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_862 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      v4
-- Data.Nat.Properties._.IsCommutativeSemiring.isEquivalence
d_isEquivalence_864 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_864 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiring.isNearSemiring
d_isNearSemiring_866 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_866 ~v0 ~v1 ~v2 ~v3 v4 = du_isNearSemiring_866 v4
du_isNearSemiring_866 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_866 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
            (coe v1)))
-- Data.Nat.Properties._.IsCommutativeSemiring.isPartialEquivalence
d_isPartialEquivalence_868 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_868 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_868 v4
du_isPartialEquivalence_868 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_868 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiring.isSemiring
d_isSemiring_870 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_870 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)
-- Data.Nat.Properties._.IsCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_872 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_872 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_874 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_874 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_874 v4
du_isSemiringWithoutOne_874 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_874 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiring.refl
d_refl_876 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_876 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.reflexive
d_reflexive_878 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_878 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.setoid
d_setoid_880 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_880 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_880 v4
du_setoid_880 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_880 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiring.sym
d_sym_882 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_882 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.trans
d_trans_884 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_884 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.zero
d_zero_886 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_886 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiring.zeroʳ
d_zero'691'_888 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_888 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.zeroˡ
d_zero'737'_890 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_890 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-assoc
d_'42''45'assoc_894 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_894 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_896 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_896 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-cong
d_'42''45'cong_898 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_898 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_900 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_900 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_902 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_902 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_904 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_904 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_904 v3
du_isCommutativeMagma_904 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_904 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_906 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_906 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
      v3
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_908 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_908 ~v0 ~v1 ~v2 v3 = du_'42''45'isMagma_908 v3
du_'42''45'isMagma_908 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_908 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1410
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_910 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_910 ~v0 ~v1 ~v2 v3
  = du_'42''45'isSemigroup_910 v3
du_'42''45'isSemigroup_910 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_910 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1412
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.assoc
d_assoc_912 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_912 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.comm
d_comm_914 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_914 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.∙-cong
d_'8729''45'cong_916 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_916 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_918 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_918 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_920 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_920 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.identity
d_identity_922 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_922 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
               (coe v0))))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.identityʳ
d_identity'691'_924 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_924 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.identityˡ
d_identity'737'_926 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_926 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_928 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_928 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_928 v3
du_isCommutativeMagma_928 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_928 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_930 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_930 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_932 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_932 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_932 v3
du_isCommutativeSemigroup_932 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_932 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe v1)))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isMonoid
d_isMonoid_934 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_934 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
            (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.distrib
d_distrib_936 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_936 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1366
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.distribʳ
d_distrib'691'_938 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_938 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.distribˡ
d_distrib'737'_940 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_940 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isEquivalence
d_isEquivalence_942 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_942 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isNearSemiring
d_isNearSemiring_944 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_944 ~v0 ~v1 ~v2 v3 = du_isNearSemiring_944 v3
du_isNearSemiring_944 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_944 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isPartialEquivalence
d_isPartialEquivalence_946 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_946 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_946 v3
du_isPartialEquivalence_946 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_946 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_948 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_948 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
      (coe v0)
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.refl
d_refl_950 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_950 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.reflexive
d_reflexive_952 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_952 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.setoid
d_setoid_954 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_954 ~v0 ~v1 ~v2 v3 = du_setoid_954 v3
du_setoid_954 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_954 v0
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
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.sym
d_sym_956 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_956 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.trans
d_trans_958 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_958 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.zero
d_zero_960 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_960 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1368
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.zeroʳ
d_zero'691'_962 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_962 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.zeroˡ
d_zero'737'_964 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_964 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.flex
d_flex_968 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flex_968 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.isEquivalence
d_isEquivalence_970 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_970 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0))
-- Data.Nat.Properties._.IsFlexibleMagma.isMagma
d_isMagma_972 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_972 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0)
-- Data.Nat.Properties._.IsFlexibleMagma.isPartialEquivalence
d_isPartialEquivalence_974 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_974 ~v0 v1 = du_isPartialEquivalence_974 v1
du_isPartialEquivalence_974 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_974 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsFlexibleMagma.refl
d_refl_976 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_976 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.reflexive
d_reflexive_978 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_978 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.setoid
d_setoid_980 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_980 ~v0 v1 = du_setoid_980 v1
du_setoid_980 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_980 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0))
-- Data.Nat.Properties._.IsFlexibleMagma.sym
d_sym_982 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_982 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.trans
d_trans_984 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_984 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.∙-cong
d_'8729''45'cong_986 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_986 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.∙-congʳ
d_'8729''45'cong'691'_988 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_988 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.∙-congˡ
d_'8729''45'cong'737'_990 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_990 = erased
-- Data.Nat.Properties._.IsGroup._-_
d__'45'__994 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> Integer -> Integer
d__'45'__994 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du__'45'__1142 v0 v2
-- Data.Nat.Properties._.IsGroup._//_
d__'47''47'__996 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> Integer -> Integer
d__'47''47'__996 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 v0 v2 v4 v5
-- Data.Nat.Properties._.IsGroup._\\_
d__'92''92'__998 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> Integer -> Integer
d__'92''92'__998 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du__'92''92'__1130 v0 v2 v4 v5
-- Data.Nat.Properties._.IsGroup.assoc
d_assoc_1000 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1000 = erased
-- Data.Nat.Properties._.IsGroup.identity
d_identity_1002 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1002 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Nat.Properties._.IsGroup.identityʳ
d_identity'691'_1004 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1004 = erased
-- Data.Nat.Properties._.IsGroup.identityˡ
d_identity'737'_1006 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1006 = erased
-- Data.Nat.Properties._.IsGroup.inverse
d_inverse_1008 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1008 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1090 (coe v0)
-- Data.Nat.Properties._.IsGroup.inverseʳ
d_inverse'691'_1010 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1010 = erased
-- Data.Nat.Properties._.IsGroup.inverseˡ
d_inverse'737'_1012 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1012 = erased
-- Data.Nat.Properties._.IsGroup.isEquivalence
d_isEquivalence_1014 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1014 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))))
-- Data.Nat.Properties._.IsGroup.isInvertibleMagma
d_isInvertibleMagma_1016 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1016 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160 v3
-- Data.Nat.Properties._.IsGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1018 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_1018 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162 v3
-- Data.Nat.Properties._.IsGroup.isMagma
d_isMagma_1020 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1020 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)))
-- Data.Nat.Properties._.IsGroup.isMonoid
d_isMonoid_1022 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1022 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)
-- Data.Nat.Properties._.IsGroup.isPartialEquivalence
d_isPartialEquivalence_1024 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1024 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1024 v3
du_isPartialEquivalence_1024 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1024 v0
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
-- Data.Nat.Properties._.IsGroup.isSemigroup
d_isSemigroup_1026 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1026 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Nat.Properties._.IsGroup.isUnitalMagma
d_isUnitalMagma_1028 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1028 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_1028 v3
du_isUnitalMagma_1028 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1028 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Nat.Properties._.IsGroup.refl
d_refl_1030 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1030 = erased
-- Data.Nat.Properties._.IsGroup.reflexive
d_reflexive_1032 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1032 = erased
-- Data.Nat.Properties._.IsGroup.setoid
d_setoid_1034 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1034 ~v0 ~v1 ~v2 v3 = du_setoid_1034 v3
du_setoid_1034 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1034 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Nat.Properties._.IsGroup.sym
d_sym_1036 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1036 = erased
-- Data.Nat.Properties._.IsGroup.trans
d_trans_1038 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1038 = erased
-- Data.Nat.Properties._.IsGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_1040 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_1040 = erased
-- Data.Nat.Properties._.IsGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_1042 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_1042 = erased
-- Data.Nat.Properties._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_1044 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1044 = erased
-- Data.Nat.Properties._.IsGroup.∙-cong
d_'8729''45'cong_1046 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1046 = erased
-- Data.Nat.Properties._.IsGroup.∙-congʳ
d_'8729''45'cong'691'_1048 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1048 = erased
-- Data.Nat.Properties._.IsGroup.∙-congˡ
d_'8729''45'cong'737'_1050 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1050 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.assoc
d_assoc_1054 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1054 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.comm
d_comm_1056 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1056 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.idem
d_idem_1058 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1058 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.identity
d_identity_1060 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1060 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.identityʳ
d_identity'691'_1062 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1062 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.identityˡ
d_identity'737'_1064 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1064 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isBand
d_isBand_1066 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1066 ~v0 ~v1 v2 = du_isBand_1066 v2
du_isBand_1066 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1066 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isCommutativeBand
d_isCommutativeBand_1068 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1068 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 v2
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_1070 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1070 ~v0 ~v1 v2
  = du_isCommutativeMagma_1070 v2
du_isCommutativeMagma_1070 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1070 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_1072 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_1072 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0)
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_1074 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1074 ~v0 ~v1 v2
  = du_isCommutativeSemigroup_1074 v2
du_isCommutativeSemigroup_1074 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1074 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isEquivalence
d_isEquivalence_1076 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1076 v0
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
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isIdempotentMonoid
d_isIdempotentMonoid_1078 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1078 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 v2
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isMagma
d_isMagma_1080 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1080 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
               (coe v0))))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isMonoid
d_isMonoid_1082 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1082 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_1084 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1084 ~v0 ~v1 v2
  = du_isPartialEquivalence_1084 v2
du_isPartialEquivalence_1084 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1084 v0
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
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isSemigroup
d_isSemigroup_1086 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1086 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_1088 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1088 ~v0 ~v1 v2 = du_isUnitalMagma_1088 v2
du_isUnitalMagma_1088 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1088 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.refl
d_refl_1090 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1090 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.reflexive
d_reflexive_1092 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1092 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.setoid
d_setoid_1094 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1094 ~v0 ~v1 v2 = du_setoid_1094 v2
du_setoid_1094 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1094 v0
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
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.sym
d_sym_1096 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1096 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.trans
d_trans_1098 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1098 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.∙-cong
d_'8729''45'cong_1100 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1100 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_1102 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1102 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_1104 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1104 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.idem
d_idem_1108 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1108 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.isEquivalence
d_isEquivalence_1110 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1110 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0))
-- Data.Nat.Properties._.IsIdempotentMagma.isMagma
d_isMagma_1112 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1112 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0)
-- Data.Nat.Properties._.IsIdempotentMagma.isPartialEquivalence
d_isPartialEquivalence_1114 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1114 ~v0 v1
  = du_isPartialEquivalence_1114 v1
du_isPartialEquivalence_1114 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1114 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsIdempotentMagma.refl
d_refl_1116 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1116 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.reflexive
d_reflexive_1118 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1118 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.setoid
d_setoid_1120 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1120 ~v0 v1 = du_setoid_1120 v1
du_setoid_1120 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1120 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0))
-- Data.Nat.Properties._.IsIdempotentMagma.sym
d_sym_1122 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1122 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.trans
d_trans_1124 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1124 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.∙-cong
d_'8729''45'cong_1126 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1126 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.∙-congʳ
d_'8729''45'cong'691'_1128 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1128 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.∙-congˡ
d_'8729''45'cong'737'_1130 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1130 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.assoc
d_assoc_1134 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1134 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.idem
d_idem_1136 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1136 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.identity
d_identity_1138 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1138 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Nat.Properties._.IsIdempotentMonoid.identityʳ
d_identity'691'_1140 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1140 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.identityˡ
d_identity'737'_1142 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1142 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.isBand
d_isBand_1144 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1144 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isBand_876 v2
-- Data.Nat.Properties._.IsIdempotentMonoid.isEquivalence
d_isEquivalence_1146 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1146 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))))
-- Data.Nat.Properties._.IsIdempotentMonoid.isMagma
d_isMagma_1148 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1148 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0)))
-- Data.Nat.Properties._.IsIdempotentMonoid.isMonoid
d_isMonoid_1150 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1150 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0)
-- Data.Nat.Properties._.IsIdempotentMonoid.isPartialEquivalence
d_isPartialEquivalence_1152 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1152 ~v0 ~v1 v2
  = du_isPartialEquivalence_1152 v2
du_isPartialEquivalence_1152 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1152 v0
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
-- Data.Nat.Properties._.IsIdempotentMonoid.isSemigroup
d_isSemigroup_1154 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Nat.Properties._.IsIdempotentMonoid.isUnitalMagma
d_isUnitalMagma_1156 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1156 ~v0 ~v1 v2 = du_isUnitalMagma_1156 v2
du_isUnitalMagma_1156 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1156 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Nat.Properties._.IsIdempotentMonoid.refl
d_refl_1158 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1158 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.reflexive
d_reflexive_1160 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1160 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.setoid
d_setoid_1162 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1162 ~v0 ~v1 v2 = du_setoid_1162 v2
du_setoid_1162 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1162 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Nat.Properties._.IsIdempotentMonoid.sym
d_sym_1164 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1164 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.trans
d_trans_1166 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1166 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.∙-cong
d_'8729''45'cong_1168 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1168 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.∙-congʳ
d_'8729''45'cong'691'_1170 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1170 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.∙-congˡ
d_'8729''45'cong'737'_1172 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1172 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.*-assoc
d_'42''45'assoc_1176 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1176 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.*-cong
d_'42''45'cong_1178 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1178 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.∙-congʳ
d_'8729''45'cong'691'_1180 ::
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
d_'8729''45'cong'691'_1180 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.∙-congˡ
d_'8729''45'cong'737'_1182 ::
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
d_'8729''45'cong'737'_1182 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.*-identity
d_'42''45'identity_1184 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1184 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Nat.Properties._.IsIdempotentSemiring.identityʳ
d_identity'691'_1186 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1186 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.identityˡ
d_identity'737'_1188 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1188 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.*-isMagma
d_'42''45'isMagma_1190 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1190 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_1190 v4
du_'42''45'isMagma_1190 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1190 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Nat.Properties._.IsIdempotentSemiring.*-isMonoid
d_'42''45'isMonoid_1192 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1192 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_1192 v4
du_'42''45'isMonoid_1192 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1192 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Nat.Properties._.IsIdempotentSemiring.*-isSemigroup
d_'42''45'isSemigroup_1194 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1194 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_1194 v4
du_'42''45'isSemigroup_1194 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1194 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Nat.Properties._.IsIdempotentSemiring.assoc
d_assoc_1196 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1196 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.comm
d_comm_1198 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1198 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.∙-cong
d_'8729''45'cong_1200 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1200 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.∙-congʳ
d_'8729''45'cong'691'_1202 ::
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
d_'8729''45'cong'691'_1202 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.∙-congˡ
d_'8729''45'cong'737'_1204 ::
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
d_'8729''45'cong'737'_1204 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.+-idem
d_'43''45'idem_1206 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1206 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.identity
d_identity_1208 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1208 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))))
-- Data.Nat.Properties._.IsIdempotentSemiring.identityʳ
d_identity'691'_1210 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1210 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.identityˡ
d_identity'737'_1212 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1212 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.isBand
d_isBand_1214 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1214 ~v0 ~v1 ~v2 ~v3 v4 = du_isBand_1214 v4
du_isBand_1214 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1214 v0
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
-- Data.Nat.Properties._.IsIdempotentSemiring.isCommutativeBand
d_isCommutativeBand_1216 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1216 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeBand_1216 v4
du_isCommutativeBand_1216 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_1216 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
      (coe
         MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
         (coe v0))
-- Data.Nat.Properties._.IsIdempotentSemiring.isCommutativeMagma
d_isCommutativeMagma_1218 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1218 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_1218 v4
du_isCommutativeMagma_1218 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1218 v0
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
-- Data.Nat.Properties._.IsIdempotentSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1220 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1220 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Nat.Properties._.IsIdempotentSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_1222 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1222 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_1222 v4
du_isCommutativeSemigroup_1222 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1222 v0
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
-- Data.Nat.Properties._.IsIdempotentSemiring.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_1224 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_1224 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
      v4
-- Data.Nat.Properties._.IsIdempotentSemiring.isIdempotentMonoid
d_isIdempotentMonoid_1226 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1226 ~v0 ~v1 ~v2 ~v3 v4
  = du_isIdempotentMonoid_1226 v4
du_isIdempotentMonoid_1226 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_1226 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
      (coe
         MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
         (coe v0))
-- Data.Nat.Properties._.IsIdempotentSemiring.isMagma
d_isMagma_1228 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1228 v0
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
-- Data.Nat.Properties._.IsIdempotentSemiring.isMonoid
d_isMonoid_1230 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1230 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))))
-- Data.Nat.Properties._.IsIdempotentSemiring.isSemigroup
d_isSemigroup_1232 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1232 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))))
-- Data.Nat.Properties._.IsIdempotentSemiring.isUnitalMagma
d_isUnitalMagma_1234 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1234 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_1234 v4
du_isUnitalMagma_1234 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1234 v0
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
-- Data.Nat.Properties._.IsIdempotentSemiring.distrib
d_distrib_1236 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1236 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Nat.Properties._.IsIdempotentSemiring.distribʳ
d_distrib'691'_1238 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1238 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.distribˡ
d_distrib'737'_1240 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1240 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.isEquivalence
d_isEquivalence_1242 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1242 v0
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
-- Data.Nat.Properties._.IsIdempotentSemiring.isNearSemiring
d_isNearSemiring_1244 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_1244 ~v0 ~v1 ~v2 ~v3 v4
  = du_isNearSemiring_1244 v4
du_isNearSemiring_1244 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_1244 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
            (coe v1)))
-- Data.Nat.Properties._.IsIdempotentSemiring.isPartialEquivalence
d_isPartialEquivalence_1246 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1246 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1246 v4
du_isPartialEquivalence_1246 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1246 v0
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
-- Data.Nat.Properties._.IsIdempotentSemiring.isSemiring
d_isSemiring_1248 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_1248 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)
-- Data.Nat.Properties._.IsIdempotentSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1250 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1250 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Nat.Properties._.IsIdempotentSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_1252 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1252 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_1252 v4
du_isSemiringWithoutOne_1252 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1252 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Nat.Properties._.IsIdempotentSemiring.refl
d_refl_1254 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1254 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.reflexive
d_reflexive_1256 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1256 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.setoid
d_setoid_1258 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1258 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1258 v4
du_setoid_1258 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1258 v0
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
-- Data.Nat.Properties._.IsIdempotentSemiring.sym
d_sym_1260 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1260 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.trans
d_trans_1262 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1262 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.zero
d_zero_1264 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1264 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Nat.Properties._.IsIdempotentSemiring.zeroʳ
d_zero'691'_1266 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1266 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.zeroˡ
d_zero'737'_1268 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1268 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.inverse
d_inverse_1272 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1272 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_974 (coe v0)
-- Data.Nat.Properties._.IsInvertibleMagma.inverseʳ
d_inverse'691'_1274 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1274 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.inverseˡ
d_inverse'737'_1276 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1276 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.isEquivalence
d_isEquivalence_1278 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1278 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0))
-- Data.Nat.Properties._.IsInvertibleMagma.isMagma
d_isMagma_1280 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1280 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0)
-- Data.Nat.Properties._.IsInvertibleMagma.isPartialEquivalence
d_isPartialEquivalence_1282 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1282 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1282 v3
du_isPartialEquivalence_1282 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1282 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsInvertibleMagma.refl
d_refl_1284 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1284 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.reflexive
d_reflexive_1286 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1286 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.setoid
d_setoid_1288 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1288 ~v0 ~v1 ~v2 v3 = du_setoid_1288 v3
du_setoid_1288 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1288 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0))
-- Data.Nat.Properties._.IsInvertibleMagma.sym
d_sym_1290 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1290 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.trans
d_trans_1292 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1292 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_1294 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1294 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.∙-cong
d_'8729''45'cong_1296 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1296 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.∙-congʳ
d_'8729''45'cong'691'_1298 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1298 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.∙-congˡ
d_'8729''45'cong'737'_1300 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1300 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.identity
d_identity_1304 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1304 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_1026 (coe v0)
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.identityʳ
d_identity'691'_1306 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1306 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.identityˡ
d_identity'737'_1308 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1308 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.inverse
d_inverse_1310 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1310 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_974
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0))
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.inverseʳ
d_inverse'691'_1312 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1312 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.inverseˡ
d_inverse'737'_1314 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1314 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.isEquivalence
d_isEquivalence_1316 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1316 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_972
         (coe
            MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0)))
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_1318 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1318 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0)
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.isMagma
d_isMagma_1320 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1320 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_972
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0))
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.isPartialEquivalence
d_isPartialEquivalence_1322 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1322 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1322 v3
du_isPartialEquivalence_1322 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1322 v0
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
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.isUnitalMagma
d_isUnitalMagma_1324 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1324 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_1064 v3
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.refl
d_refl_1326 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1326 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.reflexive
d_reflexive_1328 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1328 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.setoid
d_setoid_1330 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1330 ~v0 ~v1 ~v2 v3 = du_setoid_1330 v3
du_setoid_1330 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1330 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v1)))
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.sym
d_sym_1332 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1332 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.trans
d_trans_1334 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1334 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.⁻¹-cong
d_'8315''185''45'cong_1336 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1336 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.∙-cong
d_'8729''45'cong_1338 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1338 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.∙-congʳ
d_'8729''45'cong'691'_1340 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1340 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.∙-congˡ
d_'8729''45'cong'737'_1342 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1342 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.*-assoc
d_'42''45'assoc_1346 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1346 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.*-cong
d_'42''45'cong_1348 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1348 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.∙-congʳ
d_'8729''45'cong'691'_1350 ::
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
d_'8729''45'cong'691'_1350 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.∙-congˡ
d_'8729''45'cong'737'_1352 ::
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
d_'8729''45'cong'737'_1352 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.*-identity
d_'42''45'identity_1354 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1354 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Nat.Properties._.IsKleeneAlgebra.identityʳ
d_identity'691'_1356 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1356 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.identityˡ
d_identity'737'_1358 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1358 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.*-isMagma
d_'42''45'isMagma_1360 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1360 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMagma_1360 v5
du_'42''45'isMagma_1360 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1360 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.*-isMonoid
d_'42''45'isMonoid_1362 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1362 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMonoid_1362 v5
du_'42''45'isMonoid_1362 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1362 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.*-isSemigroup
d_'42''45'isSemigroup_1364 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1364 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isSemigroup_1364 v5
du_'42''45'isSemigroup_1364 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1364 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.assoc
d_assoc_1366 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1366 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.comm
d_comm_1368 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1368 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.∙-cong
d_'8729''45'cong_1370 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1370 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.∙-congʳ
d_'8729''45'cong'691'_1372 ::
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
d_'8729''45'cong'691'_1372 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.∙-congˡ
d_'8729''45'cong'737'_1374 ::
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
d_'8729''45'cong'737'_1374 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.+-idem
d_'43''45'idem_1376 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1376 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.identity
d_identity_1378 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1378 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.identityʳ
d_identity'691'_1380 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1380 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.identityˡ
d_identity'737'_1382 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1382 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.isBand
d_isBand_1384 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1384 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isBand_1384 v5
du_isBand_1384 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1384 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.isCommutativeBand
d_isCommutativeBand_1386 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1386 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeBand_1386 v5
du_isCommutativeBand_1386 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_1386 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
         (coe
            MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
            (coe v1)))
-- Data.Nat.Properties._.IsKleeneAlgebra.isCommutativeMagma
d_isCommutativeMagma_1388 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1388 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_1388 v5
du_isCommutativeMagma_1388 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1388 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1390 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1390 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Nat.Properties._.IsKleeneAlgebra.isCommutativeSemigroup
d_isCommutativeSemigroup_1392 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1392 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_1392 v5
du_isCommutativeSemigroup_1392 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1392 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_1394 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_1394 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'43''45'isIdempotentCommutativeMonoid_1394 v5
du_'43''45'isIdempotentCommutativeMonoid_1394 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
du_'43''45'isIdempotentCommutativeMonoid_1394 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
         (coe v0))
-- Data.Nat.Properties._.IsKleeneAlgebra.isIdempotentMonoid
d_isIdempotentMonoid_1396 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1396 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isIdempotentMonoid_1396 v5
du_isIdempotentMonoid_1396 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_1396 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
         (coe
            MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
            (coe v1)))
-- Data.Nat.Properties._.IsKleeneAlgebra.isMagma
d_isMagma_1398 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1398 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.isMonoid
d_isMonoid_1400 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1400 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.isSemigroup
d_isSemigroup_1402 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1402 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.isUnitalMagma
d_isUnitalMagma_1404 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1404 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1404 v5
du_isUnitalMagma_1404 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1404 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.distrib
d_distrib_1406 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1406 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Nat.Properties._.IsKleeneAlgebra.distribʳ
d_distrib'691'_1408 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1408 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.distribˡ
d_distrib'737'_1410 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1410 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.isEquivalence
d_isEquivalence_1412 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1412 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_1414 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998
d_isIdempotentSemiring_1414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
      (coe v0)
-- Data.Nat.Properties._.IsKleeneAlgebra.isNearSemiring
d_isNearSemiring_1416 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_1416 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isNearSemiring_1416 v5
du_isNearSemiring_1416 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_1416 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.isPartialEquivalence
d_isPartialEquivalence_1418 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1418 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1418 v5
du_isPartialEquivalence_1418 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1418 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.isSemiring
d_isSemiring_1420 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_1420 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
         (coe v0))
-- Data.Nat.Properties._.IsKleeneAlgebra.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1422 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1422 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
            (coe v0)))
-- Data.Nat.Properties._.IsKleeneAlgebra.isSemiringWithoutOne
d_isSemiringWithoutOne_1424 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1424 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isSemiringWithoutOne_1424 v5
du_isSemiringWithoutOne_1424 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1424 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1)))
-- Data.Nat.Properties._.IsKleeneAlgebra.refl
d_refl_1426 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1426 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.reflexive
d_reflexive_1428 ::
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
d_reflexive_1428 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.setoid
d_setoid_1430 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1430 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_1430 v5
du_setoid_1430 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1430 v0
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
-- Data.Nat.Properties._.IsKleeneAlgebra.starDestructive
d_starDestructive_1432 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_1432 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_starDestructive_2144 (coe v0)
-- Data.Nat.Properties._.IsKleeneAlgebra.starDestructiveʳ
d_starDestructive'691'_1434 ::
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
d_starDestructive'691'_1434 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.starDestructiveˡ
d_starDestructive'737'_1436 ::
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
d_starDestructive'737'_1436 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.starExpansive
d_starExpansive_1438 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_1438 v0
  = coe MAlonzo.Code.Algebra.Structures.d_starExpansive_2142 (coe v0)
-- Data.Nat.Properties._.IsKleeneAlgebra.starExpansiveʳ
d_starExpansive'691'_1440 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starExpansive'691'_1440 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.starExpansiveˡ
d_starExpansive'737'_1442 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starExpansive'737'_1442 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.sym
d_sym_1444 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1444 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.trans
d_trans_1446 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1446 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.zero
d_zero_1448 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1448 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
            (coe v0)))
-- Data.Nat.Properties._.IsKleeneAlgebra.zeroʳ
d_zero'691'_1450 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1450 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.zeroˡ
d_zero'737'_1452 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1452 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.//-cong
d_'47''47''45'cong_1456 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1456 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.//-congʳ
d_'47''47''45'cong'691'_1458 ::
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
d_'47''47''45'cong'691'_1458 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.//-congˡ
d_'47''47''45'cong'737'_1460 ::
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
d_'47''47''45'cong'737'_1460 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.\\-cong
d_'92''92''45'cong_1462 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1462 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.\\-congʳ
d_'92''92''45'cong'691'_1464 ::
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
d_'92''92''45'cong'691'_1464 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.\\-congˡ
d_'92''92''45'cong'737'_1466 ::
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
d_'92''92''45'cong'737'_1466 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.identity
d_identity_1468 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1468 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))
-- Data.Nat.Properties._.IsLeftBolLoop.identityʳ
d_identity'691'_1470 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1470 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.identityˡ
d_identity'737'_1472 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1472 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.isEquivalence
d_isEquivalence_1474 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1474 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))))
-- Data.Nat.Properties._.IsLeftBolLoop.isLoop
d_isLoop_1476 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1476 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)
-- Data.Nat.Properties._.IsLeftBolLoop.isMagma
d_isMagma_1478 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1478 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Nat.Properties._.IsLeftBolLoop.isPartialEquivalence
d_isPartialEquivalence_1480 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1480 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1480 v4
du_isPartialEquivalence_1480 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1480 v0
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
-- Data.Nat.Properties._.IsLeftBolLoop.isQuasigroup
d_isQuasigroup_1482 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1482 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))
-- Data.Nat.Properties._.IsLeftBolLoop.leftBol
d_leftBol_1484 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1484 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.leftDivides
d_leftDivides_1486 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1486 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Nat.Properties._.IsLeftBolLoop.leftDividesʳ
d_leftDivides'691'_1488 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1488 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.leftDividesˡ
d_leftDivides'737'_1490 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1490 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.refl
d_refl_1492 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1492 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.reflexive
d_reflexive_1494 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1494 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.rightDivides
d_rightDivides_1496 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1496 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Nat.Properties._.IsLeftBolLoop.rightDividesʳ
d_rightDivides'691'_1498 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1498 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.rightDividesˡ
d_rightDivides'737'_1500 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1500 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.setoid
d_setoid_1502 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1502 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1502 v4
du_setoid_1502 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1502 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Nat.Properties._.IsLeftBolLoop.sym
d_sym_1504 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1504 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.trans
d_trans_1506 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1506 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.∙-cong
d_'8729''45'cong_1508 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1508 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.∙-congʳ
d_'8729''45'cong'691'_1510 ::
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
d_'8729''45'cong'691'_1510 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.∙-congˡ
d_'8729''45'cong'737'_1512 ::
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
d_'8729''45'cong'737'_1512 = erased
-- Data.Nat.Properties._.IsLoop.//-cong
d_'47''47''45'cong_1516 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1516 = erased
-- Data.Nat.Properties._.IsLoop.//-congʳ
d_'47''47''45'cong'691'_1518 ::
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
d_'47''47''45'cong'691'_1518 = erased
-- Data.Nat.Properties._.IsLoop.//-congˡ
d_'47''47''45'cong'737'_1520 ::
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
d_'47''47''45'cong'737'_1520 = erased
-- Data.Nat.Properties._.IsLoop.\\-cong
d_'92''92''45'cong_1522 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1522 = erased
-- Data.Nat.Properties._.IsLoop.\\-congʳ
d_'92''92''45'cong'691'_1524 ::
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
d_'92''92''45'cong'691'_1524 = erased
-- Data.Nat.Properties._.IsLoop.\\-congˡ
d_'92''92''45'cong'737'_1526 ::
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
d_'92''92''45'cong'737'_1526 = erased
-- Data.Nat.Properties._.IsLoop.identity
d_identity_1528 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1528 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_3138 (coe v0)
-- Data.Nat.Properties._.IsLoop.identityʳ
d_identity'691'_1530 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1530 = erased
-- Data.Nat.Properties._.IsLoop.identityˡ
d_identity'737'_1532 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1532 = erased
-- Data.Nat.Properties._.IsLoop.isEquivalence
d_isEquivalence_1534 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1534 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0)))
-- Data.Nat.Properties._.IsLoop.isMagma
d_isMagma_1536 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1536 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Nat.Properties._.IsLoop.isPartialEquivalence
d_isPartialEquivalence_1538 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1538 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1538 v4
du_isPartialEquivalence_1538 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1538 v0
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
-- Data.Nat.Properties._.IsLoop.isQuasigroup
d_isQuasigroup_1540 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1540 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0)
-- Data.Nat.Properties._.IsLoop.leftDivides
d_leftDivides_1542 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Nat.Properties._.IsLoop.leftDividesʳ
d_leftDivides'691'_1544 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1544 = erased
-- Data.Nat.Properties._.IsLoop.leftDividesˡ
d_leftDivides'737'_1546 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1546 = erased
-- Data.Nat.Properties._.IsLoop.refl
d_refl_1548 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1548 = erased
-- Data.Nat.Properties._.IsLoop.reflexive
d_reflexive_1550 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1550 = erased
-- Data.Nat.Properties._.IsLoop.rightDivides
d_rightDivides_1552 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1552 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Nat.Properties._.IsLoop.rightDividesʳ
d_rightDivides'691'_1554 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1554 = erased
-- Data.Nat.Properties._.IsLoop.rightDividesˡ
d_rightDivides'737'_1556 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1556 = erased
-- Data.Nat.Properties._.IsLoop.setoid
d_setoid_1558 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1558 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1558 v4
du_setoid_1558 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1558 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v1)))
-- Data.Nat.Properties._.IsLoop.sym
d_sym_1560 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1560 = erased
-- Data.Nat.Properties._.IsLoop.trans
d_trans_1562 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1562 = erased
-- Data.Nat.Properties._.IsLoop.∙-cong
d_'8729''45'cong_1564 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1564 = erased
-- Data.Nat.Properties._.IsLoop.∙-congʳ
d_'8729''45'cong'691'_1566 ::
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
d_'8729''45'cong'691'_1566 = erased
-- Data.Nat.Properties._.IsLoop.∙-congˡ
d_'8729''45'cong'737'_1568 ::
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
d_'8729''45'cong'737'_1568 = erased
-- Data.Nat.Properties._.IsMagma.isEquivalence
d_isEquivalence_1572 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1572 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0)
-- Data.Nat.Properties._.IsMagma.isPartialEquivalence
d_isPartialEquivalence_1574 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1574 ~v0 v1
  = du_isPartialEquivalence_1574 v1
du_isPartialEquivalence_1574 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1574 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0))
-- Data.Nat.Properties._.IsMagma.refl
d_refl_1576 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1576 = erased
-- Data.Nat.Properties._.IsMagma.reflexive
d_reflexive_1578 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1578 = erased
-- Data.Nat.Properties._.IsMagma.setoid
d_setoid_1580 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1580 v0 v1
  = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 v1
-- Data.Nat.Properties._.IsMagma.sym
d_sym_1582 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1582 = erased
-- Data.Nat.Properties._.IsMagma.trans
d_trans_1584 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1584 = erased
-- Data.Nat.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1586 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1586 = erased
-- Data.Nat.Properties._.IsMagma.∙-congʳ
d_'8729''45'cong'691'_1588 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1588 = erased
-- Data.Nat.Properties._.IsMagma.∙-congˡ
d_'8729''45'cong'737'_1590 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1590 = erased
-- Data.Nat.Properties._.IsMedialMagma.isEquivalence
d_isEquivalence_1594 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1594 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0))
-- Data.Nat.Properties._.IsMedialMagma.isMagma
d_isMagma_1596 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1596 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0)
-- Data.Nat.Properties._.IsMedialMagma.isPartialEquivalence
d_isPartialEquivalence_1598 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1598 ~v0 v1
  = du_isPartialEquivalence_1598 v1
du_isPartialEquivalence_1598 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1598 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsMedialMagma.medial
d_medial_1600 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_medial_1600 = erased
-- Data.Nat.Properties._.IsMedialMagma.refl
d_refl_1602 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1602 = erased
-- Data.Nat.Properties._.IsMedialMagma.reflexive
d_reflexive_1604 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1604 = erased
-- Data.Nat.Properties._.IsMedialMagma.setoid
d_setoid_1606 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1606 ~v0 v1 = du_setoid_1606 v1
du_setoid_1606 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1606 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0))
-- Data.Nat.Properties._.IsMedialMagma.sym
d_sym_1608 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1608 = erased
-- Data.Nat.Properties._.IsMedialMagma.trans
d_trans_1610 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1610 = erased
-- Data.Nat.Properties._.IsMedialMagma.∙-cong
d_'8729''45'cong_1612 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1612 = erased
-- Data.Nat.Properties._.IsMedialMagma.∙-congʳ
d_'8729''45'cong'691'_1614 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1614 = erased
-- Data.Nat.Properties._.IsMedialMagma.∙-congˡ
d_'8729''45'cong'737'_1616 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1616 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.//-cong
d_'47''47''45'cong_1620 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1620 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.//-congʳ
d_'47''47''45'cong'691'_1622 ::
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
d_'47''47''45'cong'691'_1622 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.//-congˡ
d_'47''47''45'cong'737'_1624 ::
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
d_'47''47''45'cong'737'_1624 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.\\-cong
d_'92''92''45'cong_1626 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1626 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.\\-congʳ
d_'92''92''45'cong'691'_1628 ::
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
d_'92''92''45'cong'691'_1628 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.\\-congˡ
d_'92''92''45'cong'737'_1630 ::
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
d_'92''92''45'cong'737'_1630 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.identity
d_identity_1632 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1632 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))
-- Data.Nat.Properties._.IsMiddleBolLoop.identityʳ
d_identity'691'_1634 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1634 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.identityˡ
d_identity'737'_1636 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1636 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.isEquivalence
d_isEquivalence_1638 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1638 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))))
-- Data.Nat.Properties._.IsMiddleBolLoop.isLoop
d_isLoop_1640 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1640 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)
-- Data.Nat.Properties._.IsMiddleBolLoop.isMagma
d_isMagma_1642 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1642 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Nat.Properties._.IsMiddleBolLoop.isPartialEquivalence
d_isPartialEquivalence_1644 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1644 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1644 v4
du_isPartialEquivalence_1644 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1644 v0
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
-- Data.Nat.Properties._.IsMiddleBolLoop.isQuasigroup
d_isQuasigroup_1646 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1646 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))
-- Data.Nat.Properties._.IsMiddleBolLoop.leftDivides
d_leftDivides_1648 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1648 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Nat.Properties._.IsMiddleBolLoop.leftDividesʳ
d_leftDivides'691'_1650 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1650 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.leftDividesˡ
d_leftDivides'737'_1652 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1652 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.middleBol
d_middleBol_1654 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_middleBol_1654 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.refl
d_refl_1656 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1656 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.reflexive
d_reflexive_1658 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1658 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.rightDivides
d_rightDivides_1660 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1660 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Nat.Properties._.IsMiddleBolLoop.rightDividesʳ
d_rightDivides'691'_1662 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1662 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.rightDividesˡ
d_rightDivides'737'_1664 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1664 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.setoid
d_setoid_1666 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1666 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1666 v4
du_setoid_1666 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1666 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Nat.Properties._.IsMiddleBolLoop.sym
d_sym_1668 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1668 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.trans
d_trans_1670 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1670 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.∙-cong
d_'8729''45'cong_1672 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1672 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.∙-congʳ
d_'8729''45'cong'691'_1674 ::
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
d_'8729''45'cong'691'_1674 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.∙-congˡ
d_'8729''45'cong'737'_1676 ::
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
d_'8729''45'cong'737'_1676 = erased
-- Data.Nat.Properties._.IsMonoid.assoc
d_assoc_1680 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1680 = erased
-- Data.Nat.Properties._.IsMonoid.identity
d_identity_1682 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1682 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_724 (coe v0)
-- Data.Nat.Properties._.IsMonoid.identityʳ
d_identity'691'_1684 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1684 = erased
-- Data.Nat.Properties._.IsMonoid.identityˡ
d_identity'737'_1686 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1686 = erased
-- Data.Nat.Properties._.IsMonoid.isEquivalence
d_isEquivalence_1688 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1688 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)))
-- Data.Nat.Properties._.IsMonoid.isMagma
d_isMagma_1690 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1690 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0))
-- Data.Nat.Properties._.IsMonoid.isPartialEquivalence
d_isPartialEquivalence_1692 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1692 ~v0 ~v1 v2
  = du_isPartialEquivalence_1692 v2
du_isPartialEquivalence_1692 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1692 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Nat.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1694 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1694 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)
-- Data.Nat.Properties._.IsMonoid.isUnitalMagma
d_isUnitalMagma_1696 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1696 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756 v2
-- Data.Nat.Properties._.IsMonoid.refl
d_refl_1698 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1698 = erased
-- Data.Nat.Properties._.IsMonoid.reflexive
d_reflexive_1700 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1700 = erased
-- Data.Nat.Properties._.IsMonoid.setoid
d_setoid_1702 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1702 ~v0 ~v1 v2 = du_setoid_1702 v2
du_setoid_1702 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1702 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Nat.Properties._.IsMonoid.sym
d_sym_1704 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1704 = erased
-- Data.Nat.Properties._.IsMonoid.trans
d_trans_1706 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1706 = erased
-- Data.Nat.Properties._.IsMonoid.∙-cong
d_'8729''45'cong_1708 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1708 = erased
-- Data.Nat.Properties._.IsMonoid.∙-congʳ
d_'8729''45'cong'691'_1710 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1710 = erased
-- Data.Nat.Properties._.IsMonoid.∙-congˡ
d_'8729''45'cong'737'_1712 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1712 = erased
-- Data.Nat.Properties._.IsMoufangLoop.//-cong
d_'47''47''45'cong_1716 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1716 = erased
-- Data.Nat.Properties._.IsMoufangLoop.//-congʳ
d_'47''47''45'cong'691'_1718 ::
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
d_'47''47''45'cong'691'_1718 = erased
-- Data.Nat.Properties._.IsMoufangLoop.//-congˡ
d_'47''47''45'cong'737'_1720 ::
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
d_'47''47''45'cong'737'_1720 = erased
-- Data.Nat.Properties._.IsMoufangLoop.\\-cong
d_'92''92''45'cong_1722 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1722 = erased
-- Data.Nat.Properties._.IsMoufangLoop.\\-congʳ
d_'92''92''45'cong'691'_1724 ::
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
d_'92''92''45'cong'691'_1724 = erased
-- Data.Nat.Properties._.IsMoufangLoop.\\-congˡ
d_'92''92''45'cong'737'_1726 ::
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
d_'92''92''45'cong'737'_1726 = erased
-- Data.Nat.Properties._.IsMoufangLoop.identical
d_identical_1728 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identical_1728 = erased
-- Data.Nat.Properties._.IsMoufangLoop.identity
d_identity_1730 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1730 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3216
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)))
-- Data.Nat.Properties._.IsMoufangLoop.identityʳ
d_identity'691'_1732 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1732 = erased
-- Data.Nat.Properties._.IsMoufangLoop.identityˡ
d_identity'737'_1734 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1734 = erased
-- Data.Nat.Properties._.IsMoufangLoop.isEquivalence
d_isEquivalence_1736 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1736 v0
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
-- Data.Nat.Properties._.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_1738 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202
d_isLeftBolLoop_1738 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)
-- Data.Nat.Properties._.IsMoufangLoop.isLoop
d_isLoop_1740 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1740 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isLoop_3216
      (coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))
-- Data.Nat.Properties._.IsMoufangLoop.isMagma
d_isMagma_1742 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1742 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Nat.Properties._.IsMoufangLoop.isPartialEquivalence
d_isPartialEquivalence_1744 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1744 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1744 v4
du_isPartialEquivalence_1744 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1744 v0
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
-- Data.Nat.Properties._.IsMoufangLoop.isQuasigroup
d_isQuasigroup_1746 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1746 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3216
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)))
-- Data.Nat.Properties._.IsMoufangLoop.leftBol
d_leftBol_1748 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1748 = erased
-- Data.Nat.Properties._.IsMoufangLoop.leftDivides
d_leftDivides_1750 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1750 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Nat.Properties._.IsMoufangLoop.leftDividesʳ
d_leftDivides'691'_1752 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1752 = erased
-- Data.Nat.Properties._.IsMoufangLoop.leftDividesˡ
d_leftDivides'737'_1754 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1754 = erased
-- Data.Nat.Properties._.IsMoufangLoop.refl
d_refl_1756 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1756 = erased
-- Data.Nat.Properties._.IsMoufangLoop.reflexive
d_reflexive_1758 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1758 = erased
-- Data.Nat.Properties._.IsMoufangLoop.rightBol
d_rightBol_1760 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_1760 = erased
-- Data.Nat.Properties._.IsMoufangLoop.rightDivides
d_rightDivides_1762 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1762 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Nat.Properties._.IsMoufangLoop.rightDividesʳ
d_rightDivides'691'_1764 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1764 = erased
-- Data.Nat.Properties._.IsMoufangLoop.rightDividesˡ
d_rightDivides'737'_1766 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1766 = erased
-- Data.Nat.Properties._.IsMoufangLoop.setoid
d_setoid_1768 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1768 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1768 v4
du_setoid_1768 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1768 v0
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
-- Data.Nat.Properties._.IsMoufangLoop.sym
d_sym_1770 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1770 = erased
-- Data.Nat.Properties._.IsMoufangLoop.trans
d_trans_1772 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1772 = erased
-- Data.Nat.Properties._.IsMoufangLoop.∙-cong
d_'8729''45'cong_1774 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1774 = erased
-- Data.Nat.Properties._.IsMoufangLoop.∙-congʳ
d_'8729''45'cong'691'_1776 ::
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
d_'8729''45'cong'691'_1776 = erased
-- Data.Nat.Properties._.IsMoufangLoop.∙-congˡ
d_'8729''45'cong'737'_1778 ::
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
d_'8729''45'cong'737'_1778 = erased
-- Data.Nat.Properties._.IsNearSemiring.*-assoc
d_'42''45'assoc_1782 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1782 = erased
-- Data.Nat.Properties._.IsNearSemiring.*-cong
d_'42''45'cong_1784 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1784 = erased
-- Data.Nat.Properties._.IsNearSemiring.∙-congʳ
d_'8729''45'cong'691'_1786 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1786 = erased
-- Data.Nat.Properties._.IsNearSemiring.∙-congˡ
d_'8729''45'cong'737'_1788 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1788 = erased
-- Data.Nat.Properties._.IsNearSemiring.*-isMagma
d_'42''45'isMagma_1790 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1790 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324 v3
-- Data.Nat.Properties._.IsNearSemiring.*-isSemigroup
d_'42''45'isSemigroup_1792 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1792 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326 v3
-- Data.Nat.Properties._.IsNearSemiring.assoc
d_assoc_1794 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1794 = erased
-- Data.Nat.Properties._.IsNearSemiring.∙-cong
d_'8729''45'cong_1796 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1796 = erased
-- Data.Nat.Properties._.IsNearSemiring.∙-congʳ
d_'8729''45'cong'691'_1798 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1798 = erased
-- Data.Nat.Properties._.IsNearSemiring.∙-congˡ
d_'8729''45'cong'737'_1800 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1800 = erased
-- Data.Nat.Properties._.IsNearSemiring.identity
d_identity_1802 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1802 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Nat.Properties._.IsNearSemiring.identityʳ
d_identity'691'_1804 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1804 = erased
-- Data.Nat.Properties._.IsNearSemiring.identityˡ
d_identity'737'_1806 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1806 = erased
-- Data.Nat.Properties._.IsNearSemiring.isMagma
d_isMagma_1808 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1808 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0)))
-- Data.Nat.Properties._.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1810 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1810 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0)
-- Data.Nat.Properties._.IsNearSemiring.isSemigroup
d_isSemigroup_1812 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1812 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Nat.Properties._.IsNearSemiring.isUnitalMagma
d_isUnitalMagma_1814 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1814 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_1814 v3
du_isUnitalMagma_1814 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1814 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Nat.Properties._.IsNearSemiring.distribʳ
d_distrib'691'_1816 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1816 = erased
-- Data.Nat.Properties._.IsNearSemiring.isEquivalence
d_isEquivalence_1818 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1818 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))))
-- Data.Nat.Properties._.IsNearSemiring.isPartialEquivalence
d_isPartialEquivalence_1820 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1820 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1820 v3
du_isPartialEquivalence_1820 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1820 v0
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
-- Data.Nat.Properties._.IsNearSemiring.refl
d_refl_1822 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1822 = erased
-- Data.Nat.Properties._.IsNearSemiring.reflexive
d_reflexive_1824 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1824 = erased
-- Data.Nat.Properties._.IsNearSemiring.setoid
d_setoid_1826 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1826 ~v0 ~v1 ~v2 v3 = du_setoid_1826 v3
du_setoid_1826 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1826 v0
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
-- Data.Nat.Properties._.IsNearSemiring.sym
d_sym_1828 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1828 = erased
-- Data.Nat.Properties._.IsNearSemiring.trans
d_trans_1830 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1830 = erased
-- Data.Nat.Properties._.IsNearSemiring.zeroˡ
d_zero'737'_1832 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1832 = erased
-- Data.Nat.Properties._.IsNearring.*-assoc
d_'42''45'assoc_1836 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1836 = erased
-- Data.Nat.Properties._.IsNearring.*-cong
d_'42''45'cong_1838 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1838 = erased
-- Data.Nat.Properties._.IsNearring.∙-congʳ
d_'8729''45'cong'691'_1840 ::
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
d_'8729''45'cong'691'_1840 = erased
-- Data.Nat.Properties._.IsNearring.∙-congˡ
d_'8729''45'cong'737'_1842 ::
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
d_'8729''45'cong'737'_1842 = erased
-- Data.Nat.Properties._.IsNearring.*-identity
d_'42''45'identity_1844 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1844 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2288
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Nat.Properties._.IsNearring.identityʳ
d_identity'691'_1846 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1846 = erased
-- Data.Nat.Properties._.IsNearring.identityˡ
d_identity'737'_1848 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1848 = erased
-- Data.Nat.Properties._.IsNearring.*-isMagma
d_'42''45'isMagma_1850 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1850 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMagma_1850 v5
du_'42''45'isMagma_1850 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1850 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2342
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Nat.Properties._.IsNearring.*-isMonoid
d_'42''45'isMonoid_1852 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1852 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMonoid_1852 v5
du_'42''45'isMonoid_1852 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1852 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2346
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Nat.Properties._.IsNearring.*-isSemigroup
d_'42''45'isSemigroup_1854 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1854 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isSemigroup_1854 v5
du_'42''45'isSemigroup_1854 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1854 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_2344
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Nat.Properties._.IsNearring.assoc
d_assoc_1856 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1856 = erased
-- Data.Nat.Properties._.IsNearring.∙-cong
d_'8729''45'cong_1858 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1858 = erased
-- Data.Nat.Properties._.IsNearring.∙-congʳ
d_'8729''45'cong'691'_1860 ::
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
d_'8729''45'cong'691'_1860 = erased
-- Data.Nat.Properties._.IsNearring.∙-congˡ
d_'8729''45'cong'737'_1862 ::
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
d_'8729''45'cong'737'_1862 = erased
-- Data.Nat.Properties._.IsNearring.identity
d_identity_1864 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1864 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))
-- Data.Nat.Properties._.IsNearring.identityʳ
d_identity'691'_1866 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1866 = erased
-- Data.Nat.Properties._.IsNearring.identityˡ
d_identity'737'_1868 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1868 = erased
-- Data.Nat.Properties._.IsNearring.+-inverse
d_'43''45'inverse_1870 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_1870 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'inverse_2646 (coe v0)
-- Data.Nat.Properties._.IsNearring.+-inverseʳ
d_'43''45'inverse'691'_1872 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'691'_1872 = erased
-- Data.Nat.Properties._.IsNearring.+-inverseˡ
d_'43''45'inverse'737'_1874 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'737'_1874 = erased
-- Data.Nat.Properties._.IsNearring.isMagma
d_isMagma_1876 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1876 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
            (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))))
-- Data.Nat.Properties._.IsNearring.+-isMonoid
d_'43''45'isMonoid_1878 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1878 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Nat.Properties._.IsNearring.isSemigroup
d_isSemigroup_1880 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1880 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))
-- Data.Nat.Properties._.IsNearring.isUnitalMagma
d_isUnitalMagma_1882 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1882 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1882 v5
du_isUnitalMagma_1882 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1882 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v1)))
-- Data.Nat.Properties._.IsNearring.distrib
d_distrib_1884 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1884 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2290
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Nat.Properties._.IsNearring.distribʳ
d_distrib'691'_1886 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1886 = erased
-- Data.Nat.Properties._.IsNearring.distribˡ
d_distrib'737'_1888 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1888 = erased
-- Data.Nat.Properties._.IsNearring.identityʳ
d_identity'691'_1890 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1890 = erased
-- Data.Nat.Properties._.IsNearring.identityˡ
d_identity'737'_1892 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1892 = erased
-- Data.Nat.Properties._.IsNearring.isEquivalence
d_isEquivalence_1894 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1894 v0
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
-- Data.Nat.Properties._.IsNearring.isPartialEquivalence
d_isPartialEquivalence_1896 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1896 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1896 v5
du_isPartialEquivalence_1896 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1896 v0
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
-- Data.Nat.Properties._.IsNearring.isQuasiring
d_isQuasiring_1898 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260
d_isQuasiring_1898 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)
-- Data.Nat.Properties._.IsNearring.refl
d_refl_1900 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1900 = erased
-- Data.Nat.Properties._.IsNearring.reflexive
d_reflexive_1902 ::
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
d_reflexive_1902 = erased
-- Data.Nat.Properties._.IsNearring.setoid
d_setoid_1904 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1904 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_1904 v5
du_setoid_1904 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1904 v0
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
-- Data.Nat.Properties._.IsNearring.sym
d_sym_1906 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1906 = erased
-- Data.Nat.Properties._.IsNearring.trans
d_trans_1908 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1908 = erased
-- Data.Nat.Properties._.IsNearring.zero
d_zero_1910 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1910 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_2292
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Nat.Properties._.IsNearring.zeroʳ
d_zero'691'_1912 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1912 = erased
-- Data.Nat.Properties._.IsNearring.zeroˡ
d_zero'737'_1914 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  (Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1914 = erased
-- Data.Nat.Properties._.IsNearring.⁻¹-cong
d_'8315''185''45'cong_1916 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1916 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing._//_
d__'47''47'__1920 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> Integer -> Integer
d__'47''47'__1920 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__1920 v0 v2
du__'47''47'__1920 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__1920 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Nat.Properties._.IsNonAssociativeRing.*-cong
d_'42''45'cong_1922 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1922 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.∙-congʳ
d_'8729''45'cong'691'_1924 ::
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
d_'8729''45'cong'691'_1924 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.∙-congˡ
d_'8729''45'cong'737'_1926 ::
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
d_'8729''45'cong'737'_1926 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.*-identity
d_'42''45'identity_1928 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1928 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2520 (coe v0)
-- Data.Nat.Properties._.IsNonAssociativeRing.*-identityʳ
d_'42''45'identity'691'_1930 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_1930 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.*-identityˡ
d_'42''45'identity'737'_1932 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_1932 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.*-isMagma
d_'42''45'isMagma_1934 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1934 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2600 v5
-- Data.Nat.Properties._.IsNonAssociativeRing.*-isUnitalMagma
d_'42''45'isUnitalMagma_1936 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_'42''45'isUnitalMagma_1936 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isUnitalMagma_2606 v5
-- Data.Nat.Properties._.IsNonAssociativeRing.assoc
d_assoc_1938 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1938 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.comm
d_comm_1940 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1940 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.∙-cong
d_'8729''45'cong_1942 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1942 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.∙-congʳ
d_'8729''45'cong'691'_1944 ::
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
d_'8729''45'cong'691'_1944 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.∙-congˡ
d_'8729''45'cong'737'_1946 ::
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
d_'8729''45'cong'737'_1946 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.identity
d_identity_1948 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1948 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
               (coe v0))))
-- Data.Nat.Properties._.IsNonAssociativeRing.identityʳ
d_identity'691'_1950 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1950 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.identityˡ
d_identity'737'_1952 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1952 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_1954 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_1954 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
      (coe v0)
-- Data.Nat.Properties._.IsNonAssociativeRing.isCommutativeMagma
d_isCommutativeMagma_1956 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1956 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_1956 v5
du_isCommutativeMagma_1956 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1956 v0
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
-- Data.Nat.Properties._.IsNonAssociativeRing.isCommutativeMonoid
d_isCommutativeMonoid_1958 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_1958 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_1958 v5
du_isCommutativeMonoid_1958 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_1958 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
         (coe v0))
-- Data.Nat.Properties._.IsNonAssociativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_1960 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1960 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_1960 v5
du_isCommutativeSemigroup_1960 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1960 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
            (coe v1)))
-- Data.Nat.Properties._.IsNonAssociativeRing.isGroup
d_isGroup_1962 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_1962 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
         (coe v0))
-- Data.Nat.Properties._.IsNonAssociativeRing.isInvertibleMagma
d_isInvertibleMagma_1964 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1964 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_1964 v5
du_isInvertibleMagma_1964 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_1964 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Nat.Properties._.IsNonAssociativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1966 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_1966 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_1966 v5
du_isInvertibleUnitalMagma_1966 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_1966 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Nat.Properties._.IsNonAssociativeRing.isMagma
d_isMagma_1968 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1968 v0
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
-- Data.Nat.Properties._.IsNonAssociativeRing.isMonoid
d_isMonoid_1970 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1970 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
            (coe v0)))
-- Data.Nat.Properties._.IsNonAssociativeRing.isSemigroup
d_isSemigroup_1972 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1972 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
               (coe v0))))
-- Data.Nat.Properties._.IsNonAssociativeRing.isUnitalMagma
d_isUnitalMagma_1974 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1974 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1974 v5
du_isUnitalMagma_1974 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1974 v0
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
-- Data.Nat.Properties._.IsNonAssociativeRing.⁻¹-cong
d_'8315''185''45'cong_1976 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1976 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.inverse
d_inverse_1978 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1978 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
            (coe v0)))
-- Data.Nat.Properties._.IsNonAssociativeRing.inverseʳ
d_inverse'691'_1980 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1980 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.inverseˡ
d_inverse'737'_1982 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1982 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.distrib
d_distrib_1984 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1984 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2522 (coe v0)
-- Data.Nat.Properties._.IsNonAssociativeRing.distribʳ
d_distrib'691'_1986 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1986 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.distribˡ
d_distrib'737'_1988 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1988 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.isEquivalence
d_isEquivalence_1990 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1990 v0
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
-- Data.Nat.Properties._.IsNonAssociativeRing.isPartialEquivalence
d_isPartialEquivalence_1992 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1992 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1992 v5
du_isPartialEquivalence_1992 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1992 v0
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
-- Data.Nat.Properties._.IsNonAssociativeRing.refl
d_refl_1994 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1994 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.reflexive
d_reflexive_1996 ::
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
d_reflexive_1996 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.setoid
d_setoid_1998 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1998 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_1998 v5
du_setoid_1998 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1998 v0
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
-- Data.Nat.Properties._.IsNonAssociativeRing.sym
d_sym_2000 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2000 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.trans
d_trans_2002 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2002 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2004 ::
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
d_unique'691''45''8315''185'_2004 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2006 ::
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
d_unique'737''45''8315''185'_2006 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.zero
d_zero_2008 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2008 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2524 (coe v0)
-- Data.Nat.Properties._.IsNonAssociativeRing.zeroʳ
d_zero'691'_2010 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2010 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.zeroˡ
d_zero'737'_2012 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2012 = erased
-- Data.Nat.Properties._.IsQuasigroup.//-cong
d_'47''47''45'cong_2016 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2016 = erased
-- Data.Nat.Properties._.IsQuasigroup.//-congʳ
d_'47''47''45'cong'691'_2018 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_2018 = erased
-- Data.Nat.Properties._.IsQuasigroup.//-congˡ
d_'47''47''45'cong'737'_2020 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_2020 = erased
-- Data.Nat.Properties._.IsQuasigroup.\\-cong
d_'92''92''45'cong_2022 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2022 = erased
-- Data.Nat.Properties._.IsQuasigroup.\\-congʳ
d_'92''92''45'cong'691'_2024 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_2024 = erased
-- Data.Nat.Properties._.IsQuasigroup.\\-congˡ
d_'92''92''45'cong'737'_2026 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_2026 = erased
-- Data.Nat.Properties._.IsQuasigroup.isEquivalence
d_isEquivalence_2028 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2028 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0))
-- Data.Nat.Properties._.IsQuasigroup.isMagma
d_isMagma_2030 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2030 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0)
-- Data.Nat.Properties._.IsQuasigroup.isPartialEquivalence
d_isPartialEquivalence_2032 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2032 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_2032 v3
du_isPartialEquivalence_2032 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2032 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsQuasigroup.leftDivides
d_leftDivides_2034 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2034 v0
  = coe MAlonzo.Code.Algebra.Structures.d_leftDivides_3062 (coe v0)
-- Data.Nat.Properties._.IsQuasigroup.leftDividesʳ
d_leftDivides'691'_2036 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_2036 = erased
-- Data.Nat.Properties._.IsQuasigroup.leftDividesˡ
d_leftDivides'737'_2038 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_2038 = erased
-- Data.Nat.Properties._.IsQuasigroup.refl
d_refl_2040 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2040 = erased
-- Data.Nat.Properties._.IsQuasigroup.reflexive
d_reflexive_2042 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2042 = erased
-- Data.Nat.Properties._.IsQuasigroup.rightDivides
d_rightDivides_2044 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2044 v0
  = coe MAlonzo.Code.Algebra.Structures.d_rightDivides_3064 (coe v0)
-- Data.Nat.Properties._.IsQuasigroup.rightDividesʳ
d_rightDivides'691'_2046 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_2046 = erased
-- Data.Nat.Properties._.IsQuasigroup.rightDividesˡ
d_rightDivides'737'_2048 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_2048 = erased
-- Data.Nat.Properties._.IsQuasigroup.setoid
d_setoid_2050 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2050 ~v0 ~v1 ~v2 v3 = du_setoid_2050 v3
du_setoid_2050 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2050 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0))
-- Data.Nat.Properties._.IsQuasigroup.sym
d_sym_2052 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2052 = erased
-- Data.Nat.Properties._.IsQuasigroup.trans
d_trans_2054 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2054 = erased
-- Data.Nat.Properties._.IsQuasigroup.∙-cong
d_'8729''45'cong_2056 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2056 = erased
-- Data.Nat.Properties._.IsQuasigroup.∙-congʳ
d_'8729''45'cong'691'_2058 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2058 = erased
-- Data.Nat.Properties._.IsQuasigroup.∙-congˡ
d_'8729''45'cong'737'_2060 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2060 = erased
-- Data.Nat.Properties._.IsQuasiring.*-assoc
d_'42''45'assoc_2064 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2064 = erased
-- Data.Nat.Properties._.IsQuasiring.*-cong
d_'42''45'cong_2066 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2066 = erased
-- Data.Nat.Properties._.IsQuasiring.∙-congʳ
d_'8729''45'cong'691'_2068 ::
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
d_'8729''45'cong'691'_2068 = erased
-- Data.Nat.Properties._.IsQuasiring.∙-congˡ
d_'8729''45'cong'737'_2070 ::
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
d_'8729''45'cong'737'_2070 = erased
-- Data.Nat.Properties._.IsQuasiring.*-identity
d_'42''45'identity_2072 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2072 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2288 (coe v0)
-- Data.Nat.Properties._.IsQuasiring.identityʳ
d_identity'691'_2074 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2074 = erased
-- Data.Nat.Properties._.IsQuasiring.identityˡ
d_identity'737'_2076 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2076 = erased
-- Data.Nat.Properties._.IsQuasiring.*-isMagma
d_'42''45'isMagma_2078 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2078 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2342 v4
-- Data.Nat.Properties._.IsQuasiring.*-isMonoid
d_'42''45'isMonoid_2080 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2080 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2346 v4
-- Data.Nat.Properties._.IsQuasiring.*-isSemigroup
d_'42''45'isSemigroup_2082 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2082 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_2344 v4
-- Data.Nat.Properties._.IsQuasiring.assoc
d_assoc_2084 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2084 = erased
-- Data.Nat.Properties._.IsQuasiring.∙-cong
d_'8729''45'cong_2086 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2086 = erased
-- Data.Nat.Properties._.IsQuasiring.∙-congʳ
d_'8729''45'cong'691'_2088 ::
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
d_'8729''45'cong'691'_2088 = erased
-- Data.Nat.Properties._.IsQuasiring.∙-congˡ
d_'8729''45'cong'737'_2090 ::
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
d_'8729''45'cong'737'_2090 = erased
-- Data.Nat.Properties._.IsQuasiring.identity
d_identity_2092 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2092 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Nat.Properties._.IsQuasiring.identityʳ
d_identity'691'_2094 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2094 = erased
-- Data.Nat.Properties._.IsQuasiring.identityˡ
d_identity'737'_2096 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2096 = erased
-- Data.Nat.Properties._.IsQuasiring.isMagma
d_isMagma_2098 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2098 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0)))
-- Data.Nat.Properties._.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_2100 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_2100 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0)
-- Data.Nat.Properties._.IsQuasiring.isSemigroup
d_isSemigroup_2102 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2102 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Nat.Properties._.IsQuasiring.isUnitalMagma
d_isUnitalMagma_2104 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2104 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2104 v4
du_isUnitalMagma_2104 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2104 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Nat.Properties._.IsQuasiring.distrib
d_distrib_2106 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2106 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2290 (coe v0)
-- Data.Nat.Properties._.IsQuasiring.distribʳ
d_distrib'691'_2108 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2108 = erased
-- Data.Nat.Properties._.IsQuasiring.distribˡ
d_distrib'737'_2110 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2110 = erased
-- Data.Nat.Properties._.IsQuasiring.identityʳ
d_identity'691'_2112 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2112 = erased
-- Data.Nat.Properties._.IsQuasiring.identityˡ
d_identity'737'_2114 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2114 = erased
-- Data.Nat.Properties._.IsQuasiring.isEquivalence
d_isEquivalence_2116 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2116 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))))
-- Data.Nat.Properties._.IsQuasiring.isPartialEquivalence
d_isPartialEquivalence_2118 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2118 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2118 v4
du_isPartialEquivalence_2118 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2118 v0
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
-- Data.Nat.Properties._.IsQuasiring.refl
d_refl_2120 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2120 = erased
-- Data.Nat.Properties._.IsQuasiring.reflexive
d_reflexive_2122 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2122 = erased
-- Data.Nat.Properties._.IsQuasiring.setoid
d_setoid_2124 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2124 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2124 v4
du_setoid_2124 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2124 v0
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
-- Data.Nat.Properties._.IsQuasiring.sym
d_sym_2126 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2126 = erased
-- Data.Nat.Properties._.IsQuasiring.trans
d_trans_2128 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2128 = erased
-- Data.Nat.Properties._.IsQuasiring.zero
d_zero_2130 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2130 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2292 (coe v0)
-- Data.Nat.Properties._.IsQuasiring.zeroʳ
d_zero'691'_2132 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2132 = erased
-- Data.Nat.Properties._.IsQuasiring.zeroˡ
d_zero'737'_2134 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2134 = erased
-- Data.Nat.Properties._.IsRightBolLoop.//-cong
d_'47''47''45'cong_2138 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2138 = erased
-- Data.Nat.Properties._.IsRightBolLoop.//-congʳ
d_'47''47''45'cong'691'_2140 ::
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
d_'47''47''45'cong'691'_2140 = erased
-- Data.Nat.Properties._.IsRightBolLoop.//-congˡ
d_'47''47''45'cong'737'_2142 ::
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
d_'47''47''45'cong'737'_2142 = erased
-- Data.Nat.Properties._.IsRightBolLoop.\\-cong
d_'92''92''45'cong_2144 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2144 = erased
-- Data.Nat.Properties._.IsRightBolLoop.\\-congʳ
d_'92''92''45'cong'691'_2146 ::
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
d_'92''92''45'cong'691'_2146 = erased
-- Data.Nat.Properties._.IsRightBolLoop.\\-congˡ
d_'92''92''45'cong'737'_2148 ::
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
d_'92''92''45'cong'737'_2148 = erased
-- Data.Nat.Properties._.IsRightBolLoop.identity
d_identity_2150 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2150 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))
-- Data.Nat.Properties._.IsRightBolLoop.identityʳ
d_identity'691'_2152 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2152 = erased
-- Data.Nat.Properties._.IsRightBolLoop.identityˡ
d_identity'737'_2154 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2154 = erased
-- Data.Nat.Properties._.IsRightBolLoop.isEquivalence
d_isEquivalence_2156 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2156 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))))
-- Data.Nat.Properties._.IsRightBolLoop.isLoop
d_isLoop_2158 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_2158 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)
-- Data.Nat.Properties._.IsRightBolLoop.isMagma
d_isMagma_2160 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2160 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Nat.Properties._.IsRightBolLoop.isPartialEquivalence
d_isPartialEquivalence_2162 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2162 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2162 v4
du_isPartialEquivalence_2162 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2162 v0
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
-- Data.Nat.Properties._.IsRightBolLoop.isQuasigroup
d_isQuasigroup_2164 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_2164 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))
-- Data.Nat.Properties._.IsRightBolLoop.leftDivides
d_leftDivides_2166 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2166 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Nat.Properties._.IsRightBolLoop.leftDividesʳ
d_leftDivides'691'_2168 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_2168 = erased
-- Data.Nat.Properties._.IsRightBolLoop.leftDividesˡ
d_leftDivides'737'_2170 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_2170 = erased
-- Data.Nat.Properties._.IsRightBolLoop.refl
d_refl_2172 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2172 = erased
-- Data.Nat.Properties._.IsRightBolLoop.reflexive
d_reflexive_2174 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2174 = erased
-- Data.Nat.Properties._.IsRightBolLoop.rightBol
d_rightBol_2176 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_2176 = erased
-- Data.Nat.Properties._.IsRightBolLoop.rightDivides
d_rightDivides_2178 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2178 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Nat.Properties._.IsRightBolLoop.rightDividesʳ
d_rightDivides'691'_2180 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_2180 = erased
-- Data.Nat.Properties._.IsRightBolLoop.rightDividesˡ
d_rightDivides'737'_2182 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_2182 = erased
-- Data.Nat.Properties._.IsRightBolLoop.setoid
d_setoid_2184 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2184 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2184 v4
du_setoid_2184 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2184 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Nat.Properties._.IsRightBolLoop.sym
d_sym_2186 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2186 = erased
-- Data.Nat.Properties._.IsRightBolLoop.trans
d_trans_2188 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2188 = erased
-- Data.Nat.Properties._.IsRightBolLoop.∙-cong
d_'8729''45'cong_2190 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2190 = erased
-- Data.Nat.Properties._.IsRightBolLoop.∙-congʳ
d_'8729''45'cong'691'_2192 ::
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
d_'8729''45'cong'691'_2192 = erased
-- Data.Nat.Properties._.IsRightBolLoop.∙-congˡ
d_'8729''45'cong'737'_2194 ::
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
d_'8729''45'cong'737'_2194 = erased
-- Data.Nat.Properties._.IsRing._//_
d__'47''47'__2198 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> Integer -> Integer
d__'47''47'__2198 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__2198 v0 v2
du__'47''47'__2198 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__2198 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Nat.Properties._.IsRing.*-assoc
d_'42''45'assoc_2200 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2200 = erased
-- Data.Nat.Properties._.IsRing.*-cong
d_'42''45'cong_2202 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2202 = erased
-- Data.Nat.Properties._.IsRing.∙-congʳ
d_'8729''45'cong'691'_2204 ::
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
d_'8729''45'cong'691'_2204 = erased
-- Data.Nat.Properties._.IsRing.∙-congˡ
d_'8729''45'cong'737'_2206 ::
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
d_'8729''45'cong'737'_2206 = erased
-- Data.Nat.Properties._.IsRing.*-identity
d_'42''45'identity_2208 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2208 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768 (coe v0)
-- Data.Nat.Properties._.IsRing.identityʳ
d_identity'691'_2210 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2210 = erased
-- Data.Nat.Properties._.IsRing.identityˡ
d_identity'737'_2212 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2212 = erased
-- Data.Nat.Properties._.IsRing.*-isMagma
d_'42''45'isMagma_2214 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2214 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMagma_2214 v0 v1 v2 v3 v5
du_'42''45'isMagma_2214 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_2214 v0 v1 v2 v3 v4
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
-- Data.Nat.Properties._.IsRing.*-isMonoid
d_'42''45'isMonoid_2216 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2216 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2860 v0 v1 v2
      v3 v5
-- Data.Nat.Properties._.IsRing.*-isSemigroup
d_'42''45'isSemigroup_2218 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2218 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isSemigroup_2218 v0 v1 v2 v3 v5
du_'42''45'isSemigroup_2218 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_2218 v0 v1 v2 v3 v4
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
-- Data.Nat.Properties._.IsRing.assoc
d_assoc_2220 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2220 = erased
-- Data.Nat.Properties._.IsRing.comm
d_comm_2222 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2222 = erased
-- Data.Nat.Properties._.IsRing.∙-cong
d_'8729''45'cong_2224 ::
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
d_'8729''45'cong_2224 = erased
-- Data.Nat.Properties._.IsRing.∙-congʳ
d_'8729''45'cong'691'_2226 ::
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
d_'8729''45'cong'691'_2226 = erased
-- Data.Nat.Properties._.IsRing.∙-congˡ
d_'8729''45'cong'737'_2228 ::
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
d_'8729''45'cong'737'_2228 = erased
-- Data.Nat.Properties._.IsRing.identity
d_identity_2230 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2230 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_2230 v5
du_identity_2230 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2230 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
               (coe v0))))
-- Data.Nat.Properties._.IsRing.identityʳ
d_identity'691'_2232 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2232 = erased
-- Data.Nat.Properties._.IsRing.identityˡ
d_identity'737'_2234 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2234 = erased
-- Data.Nat.Properties._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2236 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2236 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe v0)
-- Data.Nat.Properties._.IsRing.isCommutativeMagma
d_isCommutativeMagma_2238 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2238 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_2238 v5
du_isCommutativeMagma_2238 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2238 v0
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
-- Data.Nat.Properties._.IsRing.isCommutativeMonoid
d_isCommutativeMonoid_2240 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2240 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_2240 v5
du_isCommutativeMonoid_2240 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2240 v0
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
-- Data.Nat.Properties._.IsRing.isCommutativeSemigroup
d_isCommutativeSemigroup_2242 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2242 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_2242 v5
du_isCommutativeSemigroup_2242 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2242 v0
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
-- Data.Nat.Properties._.IsRing.isGroup
d_isGroup_2244 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_2244 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_2244 v5
du_isGroup_2244 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
du_isGroup_2244 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
         (coe v0))
-- Data.Nat.Properties._.IsRing.isInvertibleMagma
d_isInvertibleMagma_2246 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_2246 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_2246 v5
du_isInvertibleMagma_2246 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_2246 v0
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
-- Data.Nat.Properties._.IsRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2248 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2248 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_2248 v5
du_isInvertibleUnitalMagma_2248 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2248 v0
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
-- Data.Nat.Properties._.IsRing.isMagma
d_isMagma_2250 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2250 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_2250 v5
du_isMagma_2250 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2250 v0
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
-- Data.Nat.Properties._.IsRing.isMonoid
d_isMonoid_2252 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2252 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_2252 v5
du_isMonoid_2252 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_isMonoid_2252 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v0)))
-- Data.Nat.Properties._.IsRing.isSemigroup
d_isSemigroup_2254 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2254 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_2254 v5
du_isSemigroup_2254 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2254 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
               (coe v0))))
-- Data.Nat.Properties._.IsRing.isUnitalMagma
d_isUnitalMagma_2256 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2256 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_2256 v5
du_isUnitalMagma_2256 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2256 v0
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
-- Data.Nat.Properties._.IsRing.⁻¹-cong
d_'8315''185''45'cong_2258 ::
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
d_'8315''185''45'cong_2258 = erased
-- Data.Nat.Properties._.IsRing.inverse
d_inverse_2260 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2260 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_2260 v5
du_inverse_2260 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2260 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v0)))
-- Data.Nat.Properties._.IsRing.inverseʳ
d_inverse'691'_2262 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_2262 = erased
-- Data.Nat.Properties._.IsRing.inverseˡ
d_inverse'737'_2264 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_2264 = erased
-- Data.Nat.Properties._.IsRing.distrib
d_distrib_2266 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2266 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2770 (coe v0)
-- Data.Nat.Properties._.IsRing.distribʳ
d_distrib'691'_2268 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2268 = erased
-- Data.Nat.Properties._.IsRing.distribˡ
d_distrib'737'_2270 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2270 = erased
-- Data.Nat.Properties._.IsRing.isEquivalence
d_isEquivalence_2272 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2272 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_2272 v5
du_isEquivalence_2272 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2272 v0
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
-- Data.Nat.Properties._.IsRing.isNearSemiring
d_isNearSemiring_2274 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2274 v0 v1 v2 v3 ~v4 v5
  = du_isNearSemiring_2274 v0 v1 v2 v3 v5
du_isNearSemiring_2274 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_2274 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v4))
-- Data.Nat.Properties._.IsRing.isPartialEquivalence
d_isPartialEquivalence_2276 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2276 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_2276 v5
du_isPartialEquivalence_2276 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2276 v0
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
-- Data.Nat.Properties._.IsRing.isRingWithoutOne
d_isRingWithoutOne_2278 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
d_isRingWithoutOne_2278 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 v5
-- Data.Nat.Properties._.IsRing.isSemiring
d_isSemiring_2280 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_2280 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 v0 v1 v2 v3 v5
-- Data.Nat.Properties._.IsRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2282 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2282 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2868
      v5
-- Data.Nat.Properties._.IsRing.isSemiringWithoutOne
d_isSemiringWithoutOne_2284 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2284 v0 v1 v2 v3 ~v4 v5
  = du_isSemiringWithoutOne_2284 v0 v1 v2 v3 v5
du_isSemiringWithoutOne_2284 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2284 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Nat.Properties._.IsRing.refl
d_refl_2286 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2286 = erased
-- Data.Nat.Properties._.IsRing.reflexive
d_reflexive_2288 ::
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
d_reflexive_2288 = erased
-- Data.Nat.Properties._.IsRing.setoid
d_setoid_2290 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2290 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_2290 v5
du_setoid_2290 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2290 v0
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
-- Data.Nat.Properties._.IsRing.sym
d_sym_2292 ::
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
d_sym_2292 = erased
-- Data.Nat.Properties._.IsRing.trans
d_trans_2294 ::
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
d_trans_2294 = erased
-- Data.Nat.Properties._.IsRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2296 ::
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
d_unique'691''45''8315''185'_2296 = erased
-- Data.Nat.Properties._.IsRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2298 ::
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
d_unique'737''45''8315''185'_2298 = erased
-- Data.Nat.Properties._.IsRing.zero
d_zero_2300 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2300 v0 v1 v2 v3 ~v4 v5 = du_zero_2300 v0 v1 v2 v3 v5
du_zero_2300 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2300 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_zero_2468 (coe v0) (coe v1)
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v4))
-- Data.Nat.Properties._.IsRing.zeroʳ
d_zero'691'_2302 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2302 = erased
-- Data.Nat.Properties._.IsRing.zeroˡ
d_zero'737'_2304 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2304 = erased
-- Data.Nat.Properties._.IsRingWithoutOne._//_
d__'47''47'__2308 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> Integer -> Integer
d__'47''47'__2308 v0 ~v1 v2 ~v3 ~v4 = du__'47''47'__2308 v0 v2
du__'47''47'__2308 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) -> Integer -> Integer -> Integer
du__'47''47'__2308 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Nat.Properties._.IsRingWithoutOne.*-assoc
d_'42''45'assoc_2310 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2310 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.*-cong
d_'42''45'cong_2312 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2312 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2314 ::
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
d_'8729''45'cong'691'_2314 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2316 ::
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
d_'8729''45'cong'737'_2316 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.*-isMagma
d_'42''45'isMagma_2318 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2318 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Nat.Properties._.IsRingWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2320 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2320 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Nat.Properties._.IsRingWithoutOne.assoc
d_assoc_2322 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2322 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.comm
d_comm_2324 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2324 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.∙-cong
d_'8729''45'cong_2326 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2326 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2328 ::
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
d_'8729''45'cong'691'_2328 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2330 ::
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
d_'8729''45'cong'737'_2330 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.identity
d_identity_2332 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2332 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
               (coe v0))))
-- Data.Nat.Properties._.IsRingWithoutOne.identityʳ
d_identity'691'_2334 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2334 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.identityˡ
d_identity'737'_2336 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2336 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2338 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2338 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
      (coe v0)
-- Data.Nat.Properties._.IsRingWithoutOne.isCommutativeMagma
d_isCommutativeMagma_2340 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2340 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2340 v4
du_isCommutativeMagma_2340 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2340 v0
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
-- Data.Nat.Properties._.IsRingWithoutOne.isCommutativeMonoid
d_isCommutativeMonoid_2342 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2342 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMonoid_2342 v4
du_isCommutativeMonoid_2342 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2342 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
         (coe v0))
-- Data.Nat.Properties._.IsRingWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_2344 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2344 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2344 v4
du_isCommutativeSemigroup_2344 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2344 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
            (coe v1)))
-- Data.Nat.Properties._.IsRingWithoutOne.isGroup
d_isGroup_2346 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_2346 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
         (coe v0))
-- Data.Nat.Properties._.IsRingWithoutOne.isInvertibleMagma
d_isInvertibleMagma_2348 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_2348 ~v0 ~v1 ~v2 ~v3 v4
  = du_isInvertibleMagma_2348 v4
du_isInvertibleMagma_2348 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_2348 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Nat.Properties._.IsRingWithoutOne.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2350 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2350 ~v0 ~v1 ~v2 ~v3 v4
  = du_isInvertibleUnitalMagma_2350 v4
du_isInvertibleUnitalMagma_2350 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2350 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Nat.Properties._.IsRingWithoutOne.isMagma
d_isMagma_2352 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2352 v0
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
-- Data.Nat.Properties._.IsRingWithoutOne.isMonoid
d_isMonoid_2354 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2354 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
            (coe v0)))
-- Data.Nat.Properties._.IsRingWithoutOne.isSemigroup
d_isSemigroup_2356 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2356 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
               (coe v0))))
-- Data.Nat.Properties._.IsRingWithoutOne.isUnitalMagma
d_isUnitalMagma_2358 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2358 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2358 v4
du_isUnitalMagma_2358 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2358 v0
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
-- Data.Nat.Properties._.IsRingWithoutOne.⁻¹-cong
d_'8315''185''45'cong_2360 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2360 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.inverse
d_inverse_2362 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2362 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
            (coe v0)))
-- Data.Nat.Properties._.IsRingWithoutOne.inverseʳ
d_inverse'691'_2364 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_2364 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.inverseˡ
d_inverse'737'_2366 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_2366 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.distrib
d_distrib_2368 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2368 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2392 (coe v0)
-- Data.Nat.Properties._.IsRingWithoutOne.distribʳ
d_distrib'691'_2370 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2370 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.distribˡ
d_distrib'737'_2372 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2372 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.isEquivalence
d_isEquivalence_2374 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2374 v0
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
-- Data.Nat.Properties._.IsRingWithoutOne.isNearSemiring
d_isNearSemiring_2376 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2376
  = coe MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470
-- Data.Nat.Properties._.IsRingWithoutOne.isPartialEquivalence
d_isPartialEquivalence_2378 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2378 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2378 v4
du_isPartialEquivalence_2378 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2378 v0
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
-- Data.Nat.Properties._.IsRingWithoutOne.refl
d_refl_2380 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2380 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.reflexive
d_reflexive_2382 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2382 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.setoid
d_setoid_2384 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2384 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2384 v4
du_setoid_2384 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2384 v0
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
-- Data.Nat.Properties._.IsRingWithoutOne.sym
d_sym_2386 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2386 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.trans
d_trans_2388 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2388 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2390 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2390 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2392 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2392 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.zero
d_zero_2394 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2394 = coe MAlonzo.Code.Algebra.Structures.du_zero_2468
-- Data.Nat.Properties._.IsRingWithoutOne.zeroʳ
d_zero'691'_2396 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2396 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.zeroˡ
d_zero'737'_2398 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2398 = erased
-- Data.Nat.Properties._.IsSelectiveMagma.isEquivalence
d_isEquivalence_2402 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2402 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0))
-- Data.Nat.Properties._.IsSelectiveMagma.isMagma
d_isMagma_2404 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2404 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0)
-- Data.Nat.Properties._.IsSelectiveMagma.isPartialEquivalence
d_isPartialEquivalence_2406 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2406 ~v0 v1
  = du_isPartialEquivalence_2406 v1
du_isPartialEquivalence_2406 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2406 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsSelectiveMagma.refl
d_refl_2408 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2408 = erased
-- Data.Nat.Properties._.IsSelectiveMagma.reflexive
d_reflexive_2410 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2410 = erased
-- Data.Nat.Properties._.IsSelectiveMagma.sel
d_sel_2412 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_2412 v0
  = coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0)
-- Data.Nat.Properties._.IsSelectiveMagma.setoid
d_setoid_2414 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2414 ~v0 v1 = du_setoid_2414 v1
du_setoid_2414 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0))
-- Data.Nat.Properties._.IsSelectiveMagma.sym
d_sym_2416 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2416 = erased
-- Data.Nat.Properties._.IsSelectiveMagma.trans
d_trans_2418 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2418 = erased
-- Data.Nat.Properties._.IsSelectiveMagma.∙-cong
d_'8729''45'cong_2420 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2420 = erased
-- Data.Nat.Properties._.IsSelectiveMagma.∙-congʳ
d_'8729''45'cong'691'_2422 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2422 = erased
-- Data.Nat.Properties._.IsSelectiveMagma.∙-congˡ
d_'8729''45'cong'737'_2424 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2424 = erased
-- Data.Nat.Properties._.IsSemigroup.assoc
d_assoc_2428 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2428 = erased
-- Data.Nat.Properties._.IsSemigroup.isEquivalence
d_isEquivalence_2430 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2430 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0))
-- Data.Nat.Properties._.IsSemigroup.isMagma
d_isMagma_2432 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2432 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Data.Nat.Properties._.IsSemigroup.isPartialEquivalence
d_isPartialEquivalence_2434 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2434 ~v0 v1
  = du_isPartialEquivalence_2434 v1
du_isPartialEquivalence_2434 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2434 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsSemigroup.refl
d_refl_2436 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2436 = erased
-- Data.Nat.Properties._.IsSemigroup.reflexive
d_reflexive_2438 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2438 = erased
-- Data.Nat.Properties._.IsSemigroup.setoid
d_setoid_2440 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2440 ~v0 v1 = du_setoid_2440 v1
du_setoid_2440 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2440 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0))
-- Data.Nat.Properties._.IsSemigroup.sym
d_sym_2442 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2442 = erased
-- Data.Nat.Properties._.IsSemigroup.trans
d_trans_2444 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2444 = erased
-- Data.Nat.Properties._.IsSemigroup.∙-cong
d_'8729''45'cong_2446 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2446 = erased
-- Data.Nat.Properties._.IsSemigroup.∙-congʳ
d_'8729''45'cong'691'_2448 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2448 = erased
-- Data.Nat.Properties._.IsSemigroup.∙-congˡ
d_'8729''45'cong'737'_2450 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2450 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.isEquivalence
d_isEquivalence_2454 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2454 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0))
-- Data.Nat.Properties._.IsSemimedialMagma.isMagma
d_isMagma_2456 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2456 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0)
-- Data.Nat.Properties._.IsSemimedialMagma.isPartialEquivalence
d_isPartialEquivalence_2458 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2458 ~v0 v1
  = du_isPartialEquivalence_2458 v1
du_isPartialEquivalence_2458 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2458 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsSemimedialMagma.refl
d_refl_2460 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2460 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.reflexive
d_reflexive_2462 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2462 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.semiMedial
d_semiMedial_2464 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_2464 v0
  = coe MAlonzo.Code.Algebra.Structures.d_semiMedial_418 (coe v0)
-- Data.Nat.Properties._.IsSemimedialMagma.semimedialʳ
d_semimedial'691'_2466 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'691'_2466 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.semimedialˡ
d_semimedial'737'_2468 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'737'_2468 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.setoid
d_setoid_2470 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2470 ~v0 v1 = du_setoid_2470 v1
du_setoid_2470 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2470 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0))
-- Data.Nat.Properties._.IsSemimedialMagma.sym
d_sym_2472 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2472 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.trans
d_trans_2474 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2474 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.∙-cong
d_'8729''45'cong_2476 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2476 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.∙-congʳ
d_'8729''45'cong'691'_2478 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2478 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.∙-congˡ
d_'8729''45'cong'737'_2480 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2480 = erased
-- Data.Nat.Properties._.IsSemiring.*-assoc
d_'42''45'assoc_2484 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2484 = erased
-- Data.Nat.Properties._.IsSemiring.*-cong
d_'42''45'cong_2486 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2486 = erased
-- Data.Nat.Properties._.IsSemiring.∙-congʳ
d_'8729''45'cong'691'_2488 ::
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
d_'8729''45'cong'691'_2488 = erased
-- Data.Nat.Properties._.IsSemiring.∙-congˡ
d_'8729''45'cong'737'_2490 ::
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
d_'8729''45'cong'737'_2490 = erased
-- Data.Nat.Properties._.IsSemiring.*-identity
d_'42''45'identity_2492 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2492 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.identityʳ
d_identity'691'_2494 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2494 = erased
-- Data.Nat.Properties._.IsSemiring.identityˡ
d_identity'737'_2496 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2496 = erased
-- Data.Nat.Properties._.IsSemiring.*-isMagma
d_'42''45'isMagma_2498 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2498 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_2498 v4
du_'42''45'isMagma_2498 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_2498 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.*-isMonoid
d_'42''45'isMonoid_2500 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2500 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_2500 v4
du_'42''45'isMonoid_2500 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_2500 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.*-isSemigroup
d_'42''45'isSemigroup_2502 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2502 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_2502 v4
du_'42''45'isSemigroup_2502 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_2502 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.assoc
d_assoc_2504 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2504 = erased
-- Data.Nat.Properties._.IsSemiring.comm
d_comm_2506 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2506 = erased
-- Data.Nat.Properties._.IsSemiring.∙-cong
d_'8729''45'cong_2508 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2508 = erased
-- Data.Nat.Properties._.IsSemiring.∙-congʳ
d_'8729''45'cong'691'_2510 ::
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
d_'8729''45'cong'691'_2510 = erased
-- Data.Nat.Properties._.IsSemiring.∙-congˡ
d_'8729''45'cong'737'_2512 ::
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
d_'8729''45'cong'737'_2512 = erased
-- Data.Nat.Properties._.IsSemiring.identity
d_identity_2514 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2514 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v0))))
-- Data.Nat.Properties._.IsSemiring.identityʳ
d_identity'691'_2516 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2516 = erased
-- Data.Nat.Properties._.IsSemiring.identityˡ
d_identity'737'_2518 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2518 = erased
-- Data.Nat.Properties._.IsSemiring.isCommutativeMagma
d_isCommutativeMagma_2520 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2520 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2520 v4
du_isCommutativeMagma_2520 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2520 v0
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
-- Data.Nat.Properties._.IsSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2522 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2522 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_2524 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2524 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2524 v4
du_isCommutativeSemigroup_2524 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2524 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v1)))
-- Data.Nat.Properties._.IsSemiring.isMagma
d_isMagma_2526 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2526 v0
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
-- Data.Nat.Properties._.IsSemiring.isMonoid
d_isMonoid_2528 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2528 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v0)))
-- Data.Nat.Properties._.IsSemiring.isSemigroup
d_isSemigroup_2530 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2530 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v0))))
-- Data.Nat.Properties._.IsSemiring.isUnitalMagma
d_isUnitalMagma_2532 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2532 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2532 v4
du_isUnitalMagma_2532 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2532 v0
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
-- Data.Nat.Properties._.IsSemiring.distrib
d_distrib_2534 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2534 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.distribʳ
d_distrib'691'_2536 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2536 = erased
-- Data.Nat.Properties._.IsSemiring.distribˡ
d_distrib'737'_2538 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2538 = erased
-- Data.Nat.Properties._.IsSemiring.isEquivalence
d_isEquivalence_2540 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2540 v0
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
-- Data.Nat.Properties._.IsSemiring.isNearSemiring
d_isNearSemiring_2542 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2542 ~v0 ~v1 ~v2 ~v3 v4
  = du_isNearSemiring_2542 v4
du_isNearSemiring_2542 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_2542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.isPartialEquivalence
d_isPartialEquivalence_2544 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2544 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2544 v4
du_isPartialEquivalence_2544 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2544 v0
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
-- Data.Nat.Properties._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2546 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2546 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe v0)
-- Data.Nat.Properties._.IsSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_2548 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2548 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730 v4
-- Data.Nat.Properties._.IsSemiring.refl
d_refl_2550 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2550 = erased
-- Data.Nat.Properties._.IsSemiring.reflexive
d_reflexive_2552 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2552 = erased
-- Data.Nat.Properties._.IsSemiring.setoid
d_setoid_2554 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2554 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2554 v4
du_setoid_2554 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2554 v0
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
-- Data.Nat.Properties._.IsSemiring.sym
d_sym_2556 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2556 = erased
-- Data.Nat.Properties._.IsSemiring.trans
d_trans_2558 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2558 = erased
-- Data.Nat.Properties._.IsSemiring.zero
d_zero_2560 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2560 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1656 (coe v0)
-- Data.Nat.Properties._.IsSemiring.zeroʳ
d_zero'691'_2562 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2562 = erased
-- Data.Nat.Properties._.IsSemiring.zeroˡ
d_zero'737'_2564 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2564 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2568 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2568 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2570 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2570 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congʳ
d_'8729''45'cong'691'_2572 ::
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
d_'8729''45'cong'691'_2572 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congˡ
d_'8729''45'cong'737'_2574 ::
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
d_'8729''45'cong'737'_2574 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2576 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2576 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562 (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.identityʳ
d_identity'691'_2578 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2578 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.identityˡ
d_identity'737'_2580 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2580 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-isMagma
d_'42''45'isMagma_2582 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2582 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614 v4
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-isMonoid
d_'42''45'isMonoid_2584 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2584 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618 v4
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-isSemigroup
d_'42''45'isSemigroup_2586 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2586 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616 v4
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.assoc
d_assoc_2588 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2588 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.comm
d_comm_2590 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2590 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.∙-cong
d_'8729''45'cong_2592 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2592 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congʳ
d_'8729''45'cong'691'_2594 ::
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
d_'8729''45'cong'691'_2594 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congˡ
d_'8729''45'cong'737'_2596 ::
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
d_'8729''45'cong'737'_2596 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.identity
d_identity_2598 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2598 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v0)))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.identityʳ
d_identity'691'_2600 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2600 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.identityˡ
d_identity'737'_2602 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2602 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isCommutativeMagma
d_isCommutativeMagma_2604 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2604 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2604 v4
du_isCommutativeMagma_2604 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2604 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2606 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2606 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isCommutativeSemigroup
d_isCommutativeSemigroup_2608 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2608 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2608 v4
du_isCommutativeSemigroup_2608 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2608 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe v0))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isMagma
d_isMagma_2610 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2610 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe v0))))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isMonoid
d_isMonoid_2612 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2612 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe v0))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isSemigroup
d_isSemigroup_2614 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2614 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v0)))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isUnitalMagma
d_isUnitalMagma_2616 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2616 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2616 v4
du_isUnitalMagma_2616 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2616 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2618 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2618 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1564 (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.distribʳ
d_distrib'691'_2620 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2620 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.distribˡ
d_distrib'737'_2622 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2622 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isEquivalence
d_isEquivalence_2624 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2624 v0
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
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isPartialEquivalence
d_isPartialEquivalence_2626 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2626 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2626 v4
du_isPartialEquivalence_2626 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2626 v0
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
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.refl
d_refl_2628 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2628 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.reflexive
d_reflexive_2630 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2630 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.setoid
d_setoid_2632 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2632 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2632 v4
du_setoid_2632 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2632 v0
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
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.sym
d_sym_2634 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2634 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.trans
d_trans_2636 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2636 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2640 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2640 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2642 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2642 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2644 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2644 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2646 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2646 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_2648 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2648 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1410 v3
-- Data.Nat.Properties._.IsSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2650 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2650 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1412 v3
-- Data.Nat.Properties._.IsSemiringWithoutOne.assoc
d_assoc_2652 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2652 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.comm
d_comm_2654 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2654 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.∙-cong
d_'8729''45'cong_2656 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2656 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2658 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2658 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2660 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2660 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.identity
d_identity_2662 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2662 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe v0)))
-- Data.Nat.Properties._.IsSemiringWithoutOne.identityʳ
d_identity'691'_2664 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2664 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.identityˡ
d_identity'737'_2666 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2666 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_2668 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2668 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_2668 v3
du_isCommutativeMagma_2668 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2668 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Nat.Properties._.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2670 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2670 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_2672 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2672 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_2672 v3
du_isCommutativeSemigroup_2672 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2672 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe v0))
-- Data.Nat.Properties._.IsSemiringWithoutOne.isMonoid
d_isMonoid_2674 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2674 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe v0))
-- Data.Nat.Properties._.IsSemiringWithoutOne.distrib
d_distrib_2676 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2676 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1366 (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutOne.distribʳ
d_distrib'691'_2678 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2678 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.distribˡ
d_distrib'737'_2680 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2680 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.isEquivalence
d_isEquivalence_2682 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2682 v0
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
-- Data.Nat.Properties._.IsSemiringWithoutOne.isNearSemiring
d_isNearSemiring_2684 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2684 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428 v3
-- Data.Nat.Properties._.IsSemiringWithoutOne.isPartialEquivalence
d_isPartialEquivalence_2686 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2686 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_2686 v3
du_isPartialEquivalence_2686 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2686 v0
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
-- Data.Nat.Properties._.IsSemiringWithoutOne.refl
d_refl_2688 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2688 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.reflexive
d_reflexive_2690 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2690 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.setoid
d_setoid_2692 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2692 ~v0 ~v1 ~v2 v3 = du_setoid_2692 v3
du_setoid_2692 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2692 v0
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
-- Data.Nat.Properties._.IsSemiringWithoutOne.sym
d_sym_2694 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2694 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.trans
d_trans_2696 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2696 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.zero
d_zero_2698 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2698 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1368 (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutOne.zeroʳ
d_zero'691'_2700 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2700 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.zeroˡ
d_zero'737'_2702 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2702 = erased
-- Data.Nat.Properties._.IsSuccessorSet.isEquivalence
d_isEquivalence_2706 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2706 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_156 (coe v0)
-- Data.Nat.Properties._.IsSuccessorSet.isPartialEquivalence
d_isPartialEquivalence_2708 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2708 ~v0 ~v1 v2
  = du_isPartialEquivalence_2708 v2
du_isPartialEquivalence_2708 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2708 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_156 (coe v0))
-- Data.Nat.Properties._.IsSuccessorSet.refl
d_refl_2710 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2710 = erased
-- Data.Nat.Properties._.IsSuccessorSet.reflexive
d_reflexive_2712 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2712 = erased
-- Data.Nat.Properties._.IsSuccessorSet.setoid
d_setoid_2714 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2714 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_setoid_172 v2
-- Data.Nat.Properties._.IsSuccessorSet.suc#-cong
d_suc'35''45'cong_2716 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'35''45'cong_2716 = erased
-- Data.Nat.Properties._.IsSuccessorSet.sym
d_sym_2718 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2718 = erased
-- Data.Nat.Properties._.IsSuccessorSet.trans
d_trans_2720 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2720 = erased
-- Data.Nat.Properties._.IsUnitalMagma.identity
d_identity_2724 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2724 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_678 (coe v0)
-- Data.Nat.Properties._.IsUnitalMagma.identityʳ
d_identity'691'_2726 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2726 = erased
-- Data.Nat.Properties._.IsUnitalMagma.identityˡ
d_identity'737'_2728 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2728 = erased
-- Data.Nat.Properties._.IsUnitalMagma.isEquivalence
d_isEquivalence_2730 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2730 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0))
-- Data.Nat.Properties._.IsUnitalMagma.isMagma
d_isMagma_2732 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2732 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0)
-- Data.Nat.Properties._.IsUnitalMagma.isPartialEquivalence
d_isPartialEquivalence_2734 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2734 ~v0 ~v1 v2
  = du_isPartialEquivalence_2734 v2
du_isPartialEquivalence_2734 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2734 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Nat.Properties._.IsUnitalMagma.refl
d_refl_2736 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2736 = erased
-- Data.Nat.Properties._.IsUnitalMagma.reflexive
d_reflexive_2738 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2738 = erased
-- Data.Nat.Properties._.IsUnitalMagma.setoid
d_setoid_2740 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2740 ~v0 ~v1 v2 = du_setoid_2740 v2
du_setoid_2740 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2740 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0))
-- Data.Nat.Properties._.IsUnitalMagma.sym
d_sym_2742 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2742 = erased
-- Data.Nat.Properties._.IsUnitalMagma.trans
d_trans_2744 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2744 = erased
-- Data.Nat.Properties._.IsUnitalMagma.∙-cong
d_'8729''45'cong_2746 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2746 = erased
-- Data.Nat.Properties._.IsUnitalMagma.∙-congʳ
d_'8729''45'cong'691'_2748 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2748 = erased
-- Data.Nat.Properties._.IsUnitalMagma.∙-congˡ
d_'8729''45'cong'737'_2750 ::
  (Integer -> Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2750 = erased
-- Data.Nat.Properties.nonZero?
d_nonZero'63'_2760 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_nonZero'63'_2760 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_constructor_120
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.Nat.Properties.nonTrivial?
d_nonTrivial'63'_2764 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_nonTrivial'63'_2764 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      1 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_constructor_162
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.Nat.Properties.suc-injective
d_suc'45'injective_2768 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'injective_2768 = erased
-- Data.Nat.Properties.≡ᵇ⇒≡
d_'8801''7495''8658''8801'_2774 ::
  Integer ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''8658''8801'_2774 = erased
-- Data.Nat.Properties.≡⇒≡ᵇ
d_'8801''8658''8801''7495'_2786 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'8801''8658''8801''7495'_2786 v0 ~v1 ~v2
  = du_'8801''8658''8801''7495'_2786 v0
du_'8801''8658''8801''7495'_2786 :: Integer -> AgdaAny
du_'8801''8658''8801''7495'_2786 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_'8801''8658''8801''7495'_2786 (coe v1))
-- Data.Nat.Properties._≟_
d__'8799'__2796 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__2796 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      erased (\ v2 -> coe du_'8801''8658''8801''7495'_2786 (coe v0))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
         (coe eqInt (coe v0) (coe v1)))
-- Data.Nat.Properties.≡-irrelevant
d_'8801''45'irrelevant_2802 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'irrelevant_2802 = erased
-- Data.Nat.Properties.≟-diag
d_'8799''45'diag_2806 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8799''45'diag_2806 = erased
-- Data.Nat.Properties.≡-isDecEquivalence
d_'8801''45'isDecEquivalence_2808 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_'8801''45'isDecEquivalence_2808
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe d__'8799'__2796)
-- Data.Nat.Properties.≡-decSetoid
d_'8801''45'decSetoid_2810 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_2810
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      d_'8801''45'isDecEquivalence_2808
-- Data.Nat.Properties.0≢1+n
d_0'8802'1'43'n_2812 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_0'8802'1'43'n_2812 = erased
-- Data.Nat.Properties.1+n≢0
d_1'43'n'8802'0_2814 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43'n'8802'0_2814 = erased
-- Data.Nat.Properties.1+n≢n
d_1'43'n'8802'n_2816 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43'n'8802'n_2816 = erased
-- Data.Nat.Properties.<ᵇ⇒<
d_'60''7495''8658''60'_2824 ::
  Integer ->
  Integer -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''7495''8658''60'_2824 v0 ~v1 ~v2
  = du_'60''7495''8658''60'_2824 v0
du_'60''7495''8658''60'_2824 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''7495''8658''60'_2824 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_'60''7495''8658''60'_2824 (coe v1)))
-- Data.Nat.Properties.<⇒<ᵇ
d_'60''8658''60''7495'_2836 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_'60''8658''60''7495'_2836 ~v0 ~v1 v2
  = du_'60''8658''60''7495'_2836 v2
du_'60''8658''60''7495'_2836 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
du_'60''8658''60''7495'_2836 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe
                    du_'60''8658''60''7495'_2836
                    (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<ᵇ-reflects-<
d_'60''7495''45'reflects'45''60'_2844 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Reflects.T_Reflects_16
d_'60''7495''45'reflects'45''60'_2844 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Reflects.du_fromEquivalence_136
      (coe ltInt (coe v0) (coe v1))
      (\ v2 -> coe du_'60''7495''8658''60'_2824 (coe v0))
      (coe du_'60''8658''60''7495'_2836)
-- Data.Nat.Properties.≤ᵇ⇒≤
d_'8804''7495''8658''8804'_2854 ::
  Integer ->
  Integer -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''7495''8658''8804'_2854 v0 ~v1 ~v2
  = du_'8804''7495''8658''8804'_2854 v0
du_'8804''7495''8658''8804'_2854 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''7495''8658''8804'_2854 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_'60''7495''8658''60'_2824 (coe v1))
-- Data.Nat.Properties.≤⇒≤ᵇ
d_'8804''8658''8804''7495'_2866 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_'8804''8658''8804''7495'_2866 ~v0 ~v1 v2
  = du_'8804''8658''8804''7495'_2866 v2
du_'8804''8658''8804''7495'_2866 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
du_'8804''8658''8804''7495'_2866 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> coe
             du_'60''8658''60''7495'_2836
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤ᵇ-reflects-≤
d_'8804''7495''45'reflects'45''8804'_2874 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Reflects.T_Reflects_16
d_'8804''7495''45'reflects'45''8804'_2874 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Reflects.du_fromEquivalence_136
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0) (coe v1))
      (\ v2 -> coe du_'8804''7495''8658''8804'_2854 (coe v0))
      (coe du_'8804''8658''8804''7495'_2866)
-- Data.Nat.Properties.≰⇒≥
d_'8816''8658''8805'_2880 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8816''8658''8805'_2880 v0 v1 ~v2
  = du_'8816''8658''8805'_2880 v0 v1
du_'8816''8658''8805'_2880 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8816''8658''8805'_2880 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe du_'8816''8658''8805'_2880 (coe v3) (coe v2))))
-- Data.Nat.Properties.≤-reflexive
d_'8804''45'reflexive_2896 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'reflexive_2896 v0 ~v1 ~v2
  = du_'8804''45'reflexive_2896 v0
du_'8804''45'reflexive_2896 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'reflexive_2896 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_'8804''45'reflexive_2896 (coe v1)))
-- Data.Nat.Properties.≤-refl
d_'8804''45'refl_2900 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'refl_2900 v0 = coe du_'8804''45'reflexive_2896 (coe v0)
-- Data.Nat.Properties.≤-antisym
d_'8804''45'antisym_2902 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_2902 = erased
-- Data.Nat.Properties.≤-trans
d_'8804''45'trans_2908 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'trans_2908 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45'trans_2908 v3 v4
du_'8804''45'trans_2908 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'trans_2908 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_'8804''45'trans_2908 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤-irrelevant
d_'8804''45'irrelevant_2914 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_2914 = erased
-- Data.Nat.Properties._≤?_
d__'8804''63'__2920 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__2920 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (\ v2 -> coe du_'8804''7495''8658''8804'_2854 (coe v0))
      (coe du_'8804''8658''8804''7495'_2866)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0) (coe v1)))
-- Data.Nat.Properties._≥?_
d__'8805''63'__2926 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''63'__2926 v0 v1
  = coe d__'8804''63'__2920 (coe v1) (coe v0)
-- Data.Nat.Properties.≤-total
d_'8804''45'total_2928 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_2928 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v2 -> coe du_'8804''7495''8658''8804'_2854 (coe v0))
              (coe du_'8804''8658''8804''7495'_2866)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
                    (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v4))
                else coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_'8816''8658''8805'_2880 (coe v0) (coe v1))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.≤-isPreorder
d_'8804''45'isPreorder_2950 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8804''45'isPreorder_2950
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_2896 v0)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45'trans_2908 v3 v4)
-- Data.Nat.Properties.≤-isTotalPreorder
d_'8804''45'isTotalPreorder_2952 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
d_'8804''45'isTotalPreorder_2952
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_178
      (coe d_'8804''45'isPreorder_2950) (coe d_'8804''45'total_2928)
-- Data.Nat.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_2954 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8804''45'isPartialOrder_2954
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe d_'8804''45'isPreorder_2950) erased
-- Data.Nat.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_2956 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8804''45'isTotalOrder_2956
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe d_'8804''45'isPartialOrder_2954) (coe d_'8804''45'total_2928)
-- Data.Nat.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_2958 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8804''45'isDecTotalOrder_2958
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe d_'8804''45'isTotalOrder_2956) (coe d__'8799'__2796)
      (coe d__'8804''63'__2920)
-- Data.Nat.Properties.≤-preorder
d_'8804''45'preorder_2960 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'8804''45'preorder_2960
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      d_'8804''45'isPreorder_2950
-- Data.Nat.Properties.≤-totalPreorder
d_'8804''45'totalPreorder_2962 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240
d_'8804''45'totalPreorder_2962
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_334
      d_'8804''45'isTotalPreorder_2952
-- Data.Nat.Properties.≤-poset
d_'8804''45'poset_2964 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8804''45'poset_2964
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      d_'8804''45'isPartialOrder_2954
-- Data.Nat.Properties.≤-totalOrder
d_'8804''45'totalOrder_2966 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_'8804''45'totalOrder_2966
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1090
      d_'8804''45'isTotalOrder_2956
-- Data.Nat.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_2968 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_'8804''45'decTotalOrder_2968
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      d_'8804''45'isDecTotalOrder_2958
-- Data.Nat.Properties.s≤s-injective
d_s'8804's'45'injective_2974 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s'8804's'45'injective_2974 = erased
-- Data.Nat.Properties.suc[m]≤n⇒m≤pred[n]
d_suc'91'm'93''8804'n'8658'm'8804'pred'91'n'93'_2976 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_suc'91'm'93''8804'n'8658'm'8804'pred'91'n'93'_2976 ~v0 v1
  = du_suc'91'm'93''8804'n'8658'm'8804'pred'91'n'93'_2976 v1
du_suc'91'm'93''8804'n'8658'm'8804'pred'91'n'93'_2976 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_suc'91'm'93''8804'n'8658'm'8804'pred'91'n'93'_2976 v0
  = case coe v0 of
      0 -> coe (\ v1 -> MAlonzo.RTE.mazUnreachableError)
      _ -> coe MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62
-- Data.Nat.Properties.m≤pred[n]⇒suc[m]≤n
d_m'8804'pred'91'n'93''8658'suc'91'm'93''8804'n_2978 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'pred'91'n'93''8658'suc'91'm'93''8804'n_2978 v0 ~v1 ~v2
  = du_m'8804'pred'91'n'93''8658'suc'91'm'93''8804'n_2978 v0
du_m'8804'pred'91'n'93''8658'suc'91'm'93''8804'n_2978 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'pred'91'n'93''8658'suc'91'm'93''8804'n_2978 v0
  = case coe v0 of
      0 -> coe (\ v1 -> MAlonzo.RTE.mazUnreachableError)
      _ -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
-- Data.Nat.Properties.≤-pred
d_'8804''45'pred_2980 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'pred_2980 ~v0 v1 = du_'8804''45'pred_2980 v1
du_'8804''45'pred_2980 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'pred_2980 v0
  = coe
      du_suc'91'm'93''8804'n'8658'm'8804'pred'91'n'93'_2976
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.m≤n⇒m≤1+n
d_m'8804'n'8658'm'8804'1'43'n_2982 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'm'8804'1'43'n_2982 ~v0 ~v1 v2
  = du_m'8804'n'8658'm'8804'1'43'n_2982 v2
du_m'8804'n'8658'm'8804'1'43'n_2982 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'm'8804'1'43'n_2982 v0 = coe v0
-- Data.Nat.Properties.n≤1+n
d_n'8804'1'43'n_2988 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'1'43'n_2988 v0 = coe d_'8804''45'refl_2900 (coe v0)
-- Data.Nat.Properties.1+n≰n
d_1'43'n'8816'n_2990 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43'n'8816'n_2990 = erased
-- Data.Nat.Properties.n≤0⇒n≡0
d_n'8804'0'8658'n'8801'0_2994 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8804'0'8658'n'8801'0_2994 = erased
-- Data.Nat.Properties.n≤1⇒n≡0∨n≡1
d_n'8804'1'8658'n'8801'0'8744'n'8801'1_2996 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_n'8804'1'8658'n'8801'0'8744'n'8801'1_2996 ~v0 v1
  = du_n'8804'1'8658'n'8801'0'8744'n'8801'1_2996 v1
du_n'8804'1'8658'n'8801'0'8744'n'8801'1_2996 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_n'8804'1'8658'n'8801'0'8744'n'8801'1_2996 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<⇒≤
d_'60''8658''8804'_2998 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8658''8804'_2998 ~v0 ~v1 v2 = du_'60''8658''8804'_2998 v2
du_'60''8658''8804'_2998 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''8658''8804'_2998 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       du_'60''8658''8804'_2998
                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<⇒≢
d_'60''8658''8802'_3002 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_3002 = erased
-- Data.Nat.Properties.>⇒≢
d_'62''8658''8802'_3006 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''8658''8802'_3006 = erased
-- Data.Nat.Properties.≤⇒≯
d_'8804''8658''8815'_3008 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_3008 = erased
-- Data.Nat.Properties.<⇒≱
d_'60''8658''8817'_3014 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_3014 = erased
-- Data.Nat.Properties.<⇒≯
d_'60''8658''8815'_3020 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8815'_3020 = erased
-- Data.Nat.Properties.≰⇒≮
d_'8816''8658''8814'_3026 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''8658''8814'_3026 = erased
-- Data.Nat.Properties.≰⇒>
d_'8816''8658''62'_3032 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8816''8658''62'_3032 v0 v1 ~v2 = du_'8816''8658''62'_3032 v0 v1
du_'8816''8658''62'_3032 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8816''8658''62'_3032 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe du_'8816''8658''62'_3032 (coe v2) (coe v3))))
-- Data.Nat.Properties.≮⇒≥
d_'8814''8658''8805'_3044 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8814''8658''8805'_3044 v0 v1 ~v2
  = du_'8814''8658''8805'_3044 v0 v1
du_'8814''8658''8805'_3044 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8814''8658''8805'_3044 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe du_'8814''8658''8805'_3044 (coe v3) (coe v2))))
-- Data.Nat.Properties.≤∧≢⇒<
d_'8804''8743''8802''8658''60'_3060 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8743''8802''8658''60'_3060 ~v0 v1 v2 ~v3
  = du_'8804''8743''8802''8658''60'_3060 v1 v2
du_'8804''8743''8802''8658''60'_3060 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8743''8802''8658''60'_3060 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe du_'8804''8743''8802''8658''60'_3060 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.≤∧≮⇒≡
d_'8804''8743''8814''8658''8801'_3078 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8743''8814''8658''8801'_3078 = erased
-- Data.Nat.Properties.≤-<-connex
d_'8804''45''60''45'connex_3084 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45''60''45'connex_3084 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v2 -> coe du_'8804''7495''8658''8804'_2854 (coe v0))
              (coe du_'8804''8658''8804''7495'_2866)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
                    (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                         -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe du_'8816''8658''62'_3032 (coe v0) (coe v1)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.≥->-connex
d_'8805''45''62''45'connex_3106 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8805''45''62''45'connex_3106 v0 v1
  = coe d_'8804''45''60''45'connex_3084 (coe v1) (coe v0)
-- Data.Nat.Properties.<-≤-connex
d_'60''45''8804''45'connex_3108 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'60''45''8804''45'connex_3108
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_flip'45'Connex_910
      (coe d_'8804''45''60''45'connex_3084)
-- Data.Nat.Properties.>-≥-connex
d_'62''45''8805''45'connex_3110 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'62''45''8805''45'connex_3110
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_flip'45'Connex_910
      (coe d_'8805''45''62''45'connex_3106)
-- Data.Nat.Properties.<-irrefl
d_'60''45'irrefl_3112 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_3112 = erased
-- Data.Nat.Properties.<-asym
d_'60''45'asym_3116 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_3116 = erased
-- Data.Nat.Properties.<-trans
d_'60''45'trans_3122 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans_3122 ~v0 v1 ~v2 v3 v4
  = du_'60''45'trans_3122 v1 v3 v4
du_'60''45'trans_3122 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'trans_3122 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe
                          du_'8804''45'trans_2908 (coe v5)
                          (coe
                             du_'8804''45'trans_2908 (coe d_n'8804'1'43'n_2988 (coe v6))
                             (coe v9)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤-<-trans
d_'8804''45''60''45'trans_3128 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45''60''45'trans_3128 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45''60''45'trans_3128 v3 v4
du_'8804''45''60''45'trans_3128 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45''60''45'trans_3128 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_'8804''45'trans_2908 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<-≤-trans
d_'60''45''8804''45'trans_3134 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45''8804''45'trans_3134 ~v0 ~v1 ~v2 v3 v4
  = du_'60''45''8804''45'trans_3134 v3 v4
du_'60''45''8804''45'trans_3134 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45''8804''45'trans_3134 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_'8804''45'trans_2908 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<-cmp
d_'60''45'cmp_3140 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_3140 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased (\ v2 -> coe du_'8801''8658''8801''7495'_2786 (coe v0))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe eqInt (coe v0) (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                         -> coe MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (let v5 = ltInt (coe v0) (coe v1) in
                        coe
                          (if coe v5
                             then coe
                                    seq
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                       (coe v5))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                       (coe du_'60''7495''8658''60'_2824 (coe v0)))
                             else coe
                                    seq
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                       (coe v5))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                       (coe
                                          du_'8804''8743''8802''8658''60'_3060 (coe v0)
                                          (coe du_'8814''8658''8805'_3044 (coe v0) (coe v1))))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties._<?_
d__'60''63'__3172 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__3172 v0 v1
  = coe
      d__'8804''63'__2920 (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe v1)
-- Data.Nat.Properties._>?_
d__'62''63'__3178 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''63'__3178 v0 v1 = coe d__'60''63'__3172 (coe v1) (coe v0)
-- Data.Nat.Properties.<-irrelevant
d_'60''45'irrelevant_3180 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_3180 = erased
-- Data.Nat.Properties.<-resp₂-≡
d_'60''45'resp'8322''45''8801'_3182 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'8322''45''8801'_3182
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_3188 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_3188
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_3122 v1 v3 v4)
      d_'60''45'resp'8322''45''8801'_3182
-- Data.Nat.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_3190 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''45'isStrictTotalOrder_3190
  = coe
      MAlonzo.Code.Relation.Binary.Structures.Biased.du_isStrictTotalOrder'7580'_620
      (coe
         MAlonzo.Code.Relation.Binary.Structures.Biased.C_constructor_638
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_3122 v1 v3 v4)
         (coe d_'60''45'cmp_3140))
-- Data.Nat.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_3192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'60''45'strictPartialOrder_3192
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      d_'60''45'isStrictPartialOrder_3188
-- Data.Nat.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_3194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_'60''45'strictTotalOrder_3194
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      d_'60''45'isStrictTotalOrder_3190
-- Data.Nat.Properties.s<s-injective
d_s'60's'45'injective_3200 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s'60's'45'injective_3200 = erased
-- Data.Nat.Properties.<-pred
d_'60''45'pred_3202 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'pred_3202 ~v0 ~v1 = du_'60''45'pred_3202
du_'60''45'pred_3202 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'pred_3202
  = coe MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70
-- Data.Nat.Properties.m<n⇒m<1+n
d_m'60'n'8658'm'60'1'43'n_3204 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'1'43'n_3204 ~v0 ~v1 v2
  = du_m'60'n'8658'm'60'1'43'n_3204 v2
du_m'60'n'8658'm'60'1'43'n_3204 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'60'1'43'n_3204 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       du_m'60'n'8658'm'60'1'43'n_3204
                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.n≮0
d_n'8814'0_3208 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8814'0_3208 = erased
-- Data.Nat.Properties.n≮n
d_n'8814'n_3212 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8814'n_3212 = erased
-- Data.Nat.Properties.0<1+n
d_0'60'1'43'n_3216 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'1'43'n_3216 ~v0 = du_0'60'1'43'n_3216
du_0'60'1'43'n_3216 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'1'43'n_3216
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Data.Nat.Properties.n<1+n
d_n'60'1'43'n_3220 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'1'43'n_3220 v0
  = coe
      d_'8804''45'refl_2900 (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.n<1⇒n≡0
d_n'60'1'8658'n'8801'0_3224 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'60'1'8658'n'8801'0_3224 = erased
-- Data.Nat.Properties.n>0⇒n≢0
d_n'62'0'8658'n'8802'0_3228 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'62'0'8658'n'8802'0_3228 = erased
-- Data.Nat.Properties.n≢0⇒n>0
d_n'8802'0'8658'n'62'0_3232 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8802'0'8658'n'62'0_3232 v0 ~v1
  = du_n'8802'0'8658'n'62'0_3232 v0
du_n'8802'0'8658'n'62'0_3232 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8802'0'8658'n'62'0_3232 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> coe du_0'60'1'43'n_3216
-- Data.Nat.Properties.m<n⇒0<n
d_m'60'n'8658'0'60'n_3238 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'0'60'n_3238 ~v0 ~v1 = du_m'60'n'8658'0'60'n_3238
du_m'60'n'8658'0'60'n_3238 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'0'60'n_3238
  = coe du_'8804''45'trans_2908 (coe du_0'60'1'43'n_3216)
-- Data.Nat.Properties.m<n⇒n≢0
d_m'60'n'8658'n'8802'0_3240 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'60'n'8658'n'8802'0_3240 = erased
-- Data.Nat.Properties.m<n⇒m≤1+n
d_m'60'n'8658'm'8804'1'43'n_3244 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'8804'1'43'n_3244 ~v0 ~v1 v2
  = du_m'60'n'8658'm'8804'1'43'n_3244 v2
du_m'60'n'8658'm'8804'1'43'n_3244 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'8804'1'43'n_3244 v0
  = coe du_'60''8658''8804'_2998 (coe v0)
-- Data.Nat.Properties.m<1+n⇒m<n∨m≡n
d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3250 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3250 v0 v1 v2
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe du_0'60'1'43'n_3216)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
                  -> let v7 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Sum.Base.du_map_84
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34) erased
                          (d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3250
                             (coe v3) (coe v7) (coe v6)))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m≤n⇒m<n∨m≡n
d_m'8804'n'8658'm'60'n'8744'm'8801'n_3260 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'8804'n'8658'm'60'n'8744'm'8801'n_3260 v0 v1 v2
  = coe
      d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3250 (coe v0) (coe v1)
      (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v2)
-- Data.Nat.Properties.m<1+n⇒m≤n
d_m'60'1'43'n'8658'm'8804'n_3264 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'1'43'n'8658'm'8804'n_3264 ~v0 ~v1 v2
  = du_m'60'1'43'n'8658'm'8804'n_3264 v2
du_m'60'1'43'n'8658'm'8804'n_3264 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'1'43'n'8658'm'8804'n_3264 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.∀[m≤n⇒m≢o]⇒n<o
d_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3274 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3274 v0 v1 ~v2
  = du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3274 v0 v1
du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3274 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3274 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe du_0'60'1'43'n_3216
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe
                             du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3274 (coe v3)
                             (coe v2))))
-- Data.Nat.Properties._.rec
d_rec_3292 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rec_3292 = erased
-- Data.Nat.Properties.∀[m<n⇒m≢o]⇒n≤o
d_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3302 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3302 v0 v1 ~v2
  = du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3302 v0 v1
du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3302 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3302 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe
                             du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3302 (coe v2)
                             (coe v3))))
-- Data.Nat.Properties._.rec
d_rec_3322 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rec_3322 = erased
-- Data.Nat.Properties.≤-Reasoning._._IsRelatedTo_
d__IsRelatedTo__3330 a0 a1 = ()
-- Data.Nat.Properties.≤-Reasoning._._∎
d__'8718'_3332 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_3332
  = let v0 = d_'8804''45'isPreorder_2950 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
            (coe v0)))
-- Data.Nat.Properties.≤-Reasoning._.<-go
d_'60''45'go_3334 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_3334
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_3122 v1 v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45''8804''45'trans_3134 v3 v4)
-- Data.Nat.Properties.≤-Reasoning._.IsEquality
d_IsEquality_3336 a0 a1 a2 = ()
-- Data.Nat.Properties.≤-Reasoning._.IsEquality?
d_IsEquality'63'_3338 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_3338 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
      v2
-- Data.Nat.Properties.≤-Reasoning._.IsStrict
d_IsStrict_3340 a0 a1 a2 = ()
-- Data.Nat.Properties.≤-Reasoning._.IsStrict?
d_IsStrict'63'_3342 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_3342 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
      v2
-- Data.Nat.Properties.≤-Reasoning._.begin_
d_begin__3344 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_begin__3344
  = let v0 = d_'8804''45'isPreorder_2950 in
    coe
      (let v1 = \ v1 v2 v3 -> coe du_'60''8658''8804'_2998 v3 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe v0) (coe v1))))
-- Data.Nat.Properties.≤-Reasoning._.begin-contradiction_
d_begin'45'contradiction__3346 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d_begin'45'contradiction__3346 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__248
-- Data.Nat.Properties.≤-Reasoning._.begin_
d_begin__3348 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__3348 = erased
-- Data.Nat.Properties.≤-Reasoning._.begin_
d_begin__3350 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_begin__3350
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
           (coe v0) v1 v2 v3)
-- Data.Nat.Properties.≤-Reasoning._.eqRelation
d_eqRelation_3352 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_3352
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
-- Data.Nat.Properties.≤-Reasoning._.extractEquality
d_extractEquality_3356 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractEquality_3356 = erased
-- Data.Nat.Properties.≤-Reasoning._.extractStrict
d_extractStrict_3358 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_extractStrict_3358 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
      v2 v3
-- Data.Nat.Properties.≤-Reasoning._.start
d_start_3366 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_start_3366
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
      (coe d_'8804''45'isPreorder_2950)
      (\ v0 v1 v2 -> coe du_'60''8658''8804'_2998 v2)
-- Data.Nat.Properties.≤-Reasoning._.step-<
d_step'45''60'_3368 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_3368
  = let v0
          = \ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_3122 v1 v3 v4 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160 in
       coe
         (let v2
                = \ v2 v3 v4 v5 v6 -> coe du_'60''45''8804''45'trans_3134 v5 v6 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe v0) (coe v1) (coe v2)))))
-- Data.Nat.Properties.≤-Reasoning._.step-≡
d_step'45''8801'_3370 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_3370
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.≤-Reasoning._.step-≡-∣
d_step'45''8801''45''8739'_3372 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_3372 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_3372 v2
du_step'45''8801''45''8739'_3372 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_3372 v0 = coe v0
-- Data.Nat.Properties.≤-Reasoning._.step-≡-⟨
d_step'45''8801''45''10216'_3374 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_3374
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.≤-Reasoning._.step-≡-⟩
d_step'45''8801''45''10217'_3376 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_3376
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.≤-Reasoning._.step-≡˘
d_step'45''8801''728'_3378 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_3378
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_454
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.≤-Reasoning._.step-≤
d_step'45''8804'_3380 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_3380
  = let v0 = d_'8804''45'isPreorder_2950 in
    coe
      (let v1
             = \ v1 v2 v3 v4 v5 -> coe du_'8804''45''60''45'trans_3128 v4 v5 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe v0) (coe v1))))
-- Data.Nat.Properties.≤-Reasoning._.stop
d_stop_3382 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_3382
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
      (coe d_'8804''45'isPreorder_2950)
-- Data.Nat.Properties.≤-Reasoning._.strictRelation
d_strictRelation_3386 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_3386
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
-- Data.Nat.Properties.≤-Reasoning._.≈-go
d_'8776''45'go_3388 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_3388
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
      (coe d_'8804''45'isPreorder_2950)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
-- Data.Nat.Properties.≤-Reasoning._.≡-go
d_'8801''45'go_3390 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_3390 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_3390 v4
du_'8801''45'go_3390 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_3390 v0 = coe v0
-- Data.Nat.Properties.≤-Reasoning._.≤-go
d_'8804''45'go_3392 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_3392
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
      (coe d_'8804''45'isPreorder_2950)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45''60''45'trans_3128 v3 v4)
-- Data.Nat.Properties.+-suc
d_'43''45'suc_3414 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'suc_3414 = erased
-- Data.Nat.Properties.+-assoc
d_'43''45'assoc_3422 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_3422 = erased
-- Data.Nat.Properties.+-identityˡ
d_'43''45'identity'737'_3430 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737'_3430 = erased
-- Data.Nat.Properties.+-identityʳ
d_'43''45'identity'691'_3432 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_3432 = erased
-- Data.Nat.Properties.+-identity
d_'43''45'identity_3436 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'identity_3436
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.+-comm
d_'43''45'comm_3438 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_3438 = erased
-- Data.Nat.Properties.+-cancelˡ-≡
d_'43''45'cancel'737''45''8801'_3446 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'737''45''8801'_3446 = erased
-- Data.Nat.Properties.+-cancelʳ-≡
d_'43''45'cancel'691''45''8801'_3454 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'691''45''8801'_3454 = erased
-- Data.Nat.Properties.+-cancel-≡
d_'43''45'cancel'45''8801'_3456 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'cancel'45''8801'_3456
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.+-isMagma
d_'43''45'isMagma_3458 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'43''45'isMagma_3458
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Nat.Properties.+-isSemigroup
d_'43''45'isSemigroup_3460 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'43''45'isSemigroup_3460
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe d_'43''45'isMagma_3458) erased
-- Data.Nat.Properties.+-isCommutativeSemigroup
d_'43''45'isCommutativeSemigroup_3462 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'43''45'isCommutativeSemigroup_3462
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_608
      (coe d_'43''45'isSemigroup_3460) erased
-- Data.Nat.Properties.+-0-isMonoid
d_'43''45'0'45'isMonoid_3464 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'0'45'isMonoid_3464
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe d_'43''45'isSemigroup_3460) (coe d_'43''45'identity_3436)
-- Data.Nat.Properties.+-0-isCommutativeMonoid
d_'43''45'0'45'isCommutativeMonoid_3466 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'0'45'isCommutativeMonoid_3466
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe d_'43''45'0'45'isMonoid_3464) erased
-- Data.Nat.Properties.+-magma
d_'43''45'magma_3468 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'43''45'magma_3468
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124 addInt
      d_'43''45'isMagma_3458
-- Data.Nat.Properties.+-semigroup
d_'43''45'semigroup_3470 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'43''45'semigroup_3470
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614 addInt
      d_'43''45'isSemigroup_3460
-- Data.Nat.Properties.+-commutativeSemigroup
d_'43''45'commutativeSemigroup_3472 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'43''45'commutativeSemigroup_3472
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_754 addInt
      d_'43''45'isCommutativeSemigroup_3462
-- Data.Nat.Properties.+-0-monoid
d_'43''45'0'45'monoid_3474 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'43''45'0'45'monoid_3474
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990 addInt
      (0 :: Integer) d_'43''45'0'45'isMonoid_3464
-- Data.Nat.Properties.+-0-commutativeMonoid
d_'43''45'0'45'commutativeMonoid_3476 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'43''45'0'45'commutativeMonoid_3476
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088 addInt
      (0 :: Integer) d_'43''45'0'45'isCommutativeMonoid_3466
-- Data.Nat.Properties.∸-magma
d_'8760''45'magma_3478 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8760''45'magma_3478
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra.du_magma_20
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22)
-- Data.Nat.Properties.m≢1+m+n
d_m'8802'1'43'm'43'n_3484 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'8802'1'43'm'43'n_3484 = erased
-- Data.Nat.Properties.m≢1+n+m
d_m'8802'1'43'n'43'm_3494 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'8802'1'43'n'43'm_3494 = erased
-- Data.Nat.Properties.m+1+n≢m
d_m'43'1'43'n'8802'm_3504 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'1'43'n'8802'm_3504 = erased
-- Data.Nat.Properties.m+1+n≢n
d_m'43'1'43'n'8802'n_3512 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'1'43'n'8802'n_3512 = erased
-- Data.Nat.Properties.m+1+n≢0
d_m'43'1'43'n'8802'0_3526 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'1'43'n'8802'0_3526 = erased
-- Data.Nat.Properties.m+n≡0⇒m≡0
d_m'43'n'8801'0'8658'm'8801'0_3540 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43'n'8801'0'8658'm'8801'0_3540 = erased
-- Data.Nat.Properties.m+n≡0⇒n≡0
d_m'43'n'8801'0'8658'n'8801'0_3548 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43'n'8801'0'8658'n'8801'0_3548 = erased
-- Data.Nat.Properties.+-cancelˡ-≤
d_'43''45'cancel'737''45''8804'_3556 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'cancel'737''45''8804'_3556 v0 ~v1 ~v2 v3
  = du_'43''45'cancel'737''45''8804'_3556 v0 v3
du_'43''45'cancel'737''45''8804'_3556 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'cancel'737''45''8804'_3556 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe du_'43''45'cancel'737''45''8804'_3556 (coe v2) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.+-cancelʳ-≤
d_'43''45'cancel'691''45''8804'_3564 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'cancel'691''45''8804'_3564 v0 ~v1 ~v2 v3
  = du_'43''45'cancel'691''45''8804'_3564 v0 v3
du_'43''45'cancel'691''45''8804'_3564 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'cancel'691''45''8804'_3564 v0 v1
  = coe du_'43''45'cancel'737''45''8804'_3556 (coe v0) (coe v1)
-- Data.Nat.Properties.+-cancel-≤
d_'43''45'cancel'45''8804'_3574 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'cancel'45''8804'_3574
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 v3 -> coe du_'43''45'cancel'737''45''8804'_3556 v0 v3)
      (\ v0 v1 v2 v3 -> coe du_'43''45'cancel'691''45''8804'_3564 v0 v3)
-- Data.Nat.Properties.+-cancelˡ-<
d_'43''45'cancel'737''45''60'_3576 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'cancel'737''45''60'_3576 v0 ~v1 ~v2 v3
  = du_'43''45'cancel'737''45''60'_3576 v0 v3
du_'43''45'cancel'737''45''60'_3576 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'cancel'737''45''60'_3576 v0 v1
  = coe du_'43''45'cancel'737''45''8804'_3556 (coe v0) (coe v1)
-- Data.Nat.Properties.+-cancelʳ-<
d_'43''45'cancel'691''45''60'_3586 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'cancel'691''45''60'_3586 v0 ~v1 ~v2 v3
  = du_'43''45'cancel'691''45''60'_3586 v0 v3
du_'43''45'cancel'691''45''60'_3586 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'cancel'691''45''60'_3586 v0 v1
  = coe du_'43''45'cancel'691''45''8804'_3564 (coe v0) (coe v1)
-- Data.Nat.Properties.+-cancel-<
d_'43''45'cancel'45''60'_3596 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'cancel'45''60'_3596
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 v3 -> coe du_'43''45'cancel'737''45''60'_3576 v0 v3)
      (\ v0 v1 v2 v3 -> coe du_'43''45'cancel'691''45''60'_3586 v0 v3)
-- Data.Nat.Properties.m≤n⇒m≤o+n
d_m'8804'n'8658'm'8804'o'43'n_3600 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'm'8804'o'43'n_3600 ~v0 ~v1 ~v2 v3
  = du_m'8804'n'8658'm'8804'o'43'n_3600 v3
du_m'8804'n'8658'm'8804'o'43'n_3600 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'm'8804'o'43'n_3600 v0 = coe v0
-- Data.Nat.Properties.m≤n⇒m≤n+o
d_m'8804'n'8658'm'8804'n'43'o_3610 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'm'8804'n'43'o_3610 ~v0 ~v1 ~v2 v3
  = du_m'8804'n'8658'm'8804'n'43'o_3610 v3
du_m'8804'n'8658'm'8804'n'43'o_3610 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'm'8804'n'43'o_3610 v0 = coe v0
-- Data.Nat.Properties.m≤m+n
d_m'8804'm'43'n_3624 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'm'43'n_3624 v0 ~v1 = du_m'8804'm'43'n_3624 v0
du_m'8804'm'43'n_3624 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'm'43'n_3624 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_m'8804'm'43'n_3624 (coe v1)))
-- Data.Nat.Properties.m≤n+m
d_m'8804'n'43'm_3636 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'm_3636 v0 ~v1 = du_m'8804'n'43'm_3636 v0
du_m'8804'n'43'm_3636 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'43'm_3636 v0 = coe du_m'8804'm'43'n_3624 (coe v0)
-- Data.Nat.Properties.m+n≤o⇒m≤o
d_m'43'n'8804'o'8658'm'8804'o_3650 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'43'n'8804'o'8658'm'8804'o_3650 v0 ~v1 ~v2 v3
  = du_m'43'n'8804'o'8658'm'8804'o_3650 v0 v3
du_m'43'n'8804'o'8658'm'8804'o_3650 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'43'n'8804'o'8658'm'8804'o_3650 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe du_m'43'n'8804'o'8658'm'8804'o_3650 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m+n≤o⇒n≤o
d_m'43'n'8804'o'8658'n'8804'o_3664 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'43'n'8804'o'8658'n'8804'o_3664 v0 ~v1 ~v2 v3
  = du_m'43'n'8804'o'8658'n'8804'o_3664 v0 v3
du_m'43'n'8804'o'8658'n'8804'o_3664 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'43'n'8804'o'8658'n'8804'o_3664 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_m'43'n'8804'o'8658'n'8804'o_3664 (coe v2)
                (coe du_'60''8658''8804'_2998 (coe v1)))
-- Data.Nat.Properties.+-mono-≤
d_'43''45'mono'45''8804'_3672 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'45''8804'_3672 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'43''45'mono'45''8804'_3672 v3 v4 v5
du_'43''45'mono'45''8804'_3672 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'45''8804'_3672 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             du_'8804''45'trans_2908 (coe v2)
             (coe du_m'8804'n'43'm_3636 (coe v0))
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_'43''45'mono'45''8804'_3672 (coe v0) (coe v5) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.+-monoˡ-≤
d_'43''45'mono'737''45''8804'_3682 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'737''45''8804'_3682
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8322''8658'mono'691'_352
      (coe d_'8804''45'refl_2900)
      (\ v0 v1 v2 v3 v4 v5 ->
         coe du_'43''45'mono'45''8804'_3672 v3 v4 v5)
-- Data.Nat.Properties.+-monoʳ-≤
d_'43''45'mono'691''45''8804'_3684 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'691''45''8804'_3684
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8322''8658'mono'737'_342
      (coe d_'8804''45'refl_2900)
      (\ v0 v1 v2 v3 v4 v5 ->
         coe du_'43''45'mono'45''8804'_3672 v3 v4 v5)
-- Data.Nat.Properties.+-mono-<-≤
d_'43''45'mono'45''60''45''8804'_3686 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'45''60''45''8804'_3686 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'43''45'mono'45''60''45''8804'_3686 v4 v5
du_'43''45'mono'45''60''45''8804'_3686 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'45''60''45''8804'_3686 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v1
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       du_'43''45'mono'45''60''45''8804'_3686
                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.+-mono-≤-<
d_'43''45'mono'45''8804''45''60'_3696 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'45''8804''45''60'_3696 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'43''45'mono'45''8804''45''60'_3696 v3 v4 v5
du_'43''45'mono'45''8804''45''60'_3696 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'45''8804''45''60'_3696 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             du_'8804''45'trans_2908 (coe v2)
             (coe du_m'8804'n'43'm_3636 (coe v0))
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe
                du_'43''45'mono'45''8804''45''60'_3696 (coe v0) (coe v5) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.+-mono-<
d_'43''45'mono'45''60'_3706 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'45''60'_3706 ~v0 ~v1 ~v2 v3 v4
  = du_'43''45'mono'45''60'_3706 v3 v4
du_'43''45'mono'45''60'_3706 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'45''60'_3706 v0 v1
  = coe
      du_'43''45'mono'45''8804''45''60'_3696 (coe v0)
      (coe du_'60''8658''8804'_2998 (coe v1))
-- Data.Nat.Properties.+-monoˡ-<
d_'43''45'mono'737''45''60'_3710 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'737''45''60'_3710 v0 v1 v2
  = coe
      d_'43''45'mono'737''45''8804'_3682 v0
      (addInt (coe (1 :: Integer)) (coe v1)) v2
-- Data.Nat.Properties.+-monoʳ-<
d_'43''45'mono'691''45''60'_3714 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'691''45''60'_3714 v0 ~v1 ~v2 v3
  = du_'43''45'mono'691''45''60'_3714 v0 v3
du_'43''45'mono'691''45''60'_3714 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'691''45''60'_3714 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_'43''45'mono'691''45''60'_3714 (coe v2) (coe v1)))
-- Data.Nat.Properties.m+1+n≰m
d_m'43'1'43'n'8816'm_3726 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'1'43'n'8816'm_3726 = erased
-- Data.Nat.Properties.m<m+n
d_m'60'm'43'n_3736 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'm'43'n_3736 v0 ~v1 v2 = du_m'60'm'43'n_3736 v0 v2
du_m'60'm'43'n_3736 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'm'43'n_3736 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_m'60'm'43'n_3736 (coe v2) (coe v1)))
-- Data.Nat.Properties.m<n+m
d_m'60'n'43'm_3748 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'43'm_3748 v0 ~v1 v2 = du_m'60'n'43'm_3748 v0 v2
du_m'60'n'43'm_3748 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'43'm_3748 v0 v1
  = coe du_m'60'm'43'n_3736 (coe v0) (coe v1)
-- Data.Nat.Properties.m+n≮n
d_m'43'n'8814'n_3764 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'n'8814'n_3764 = erased
-- Data.Nat.Properties.m+n≮m
d_m'43'n'8814'm_3778 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'n'8814'm_3778 = erased
-- Data.Nat.Properties.*-suc
d_'42''45'suc_3790 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'suc_3790 = erased
-- Data.Nat.Properties.*-identityˡ
d_'42''45'identity'737'_3802 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_3802 = erased
-- Data.Nat.Properties.*-identityʳ
d_'42''45'identity'691'_3806 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_3806 = erased
-- Data.Nat.Properties.*-identity
d_'42''45'identity_3810 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_3810
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.*-zeroˡ
d_'42''45'zero'737'_3812 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'737'_3812 = erased
-- Data.Nat.Properties.*-zeroʳ
d_'42''45'zero'691'_3814 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'691'_3814 = erased
-- Data.Nat.Properties.*-zero
d_'42''45'zero_3818 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'zero_3818
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.*-comm
d_'42''45'comm_3820 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_3820 = erased
-- Data.Nat.Properties.*-distribʳ-+
d_'42''45'distrib'691''45''43'_3830 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''43'_3830 = erased
-- Data.Nat.Properties.*-distribˡ-+
d_'42''45'distrib'737''45''43'_3844 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''43'_3844 = erased
-- Data.Nat.Properties.*-distrib-+
d_'42''45'distrib'45''43'_3846 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''43'_3846
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.*-assoc
d_'42''45'assoc_3848 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_3848 = erased
-- Data.Nat.Properties.*-isMagma
d_'42''45'isMagma_3862 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_3862
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Nat.Properties.*-isSemigroup
d_'42''45'isSemigroup_3864 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_3864
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe d_'42''45'isMagma_3862) erased
-- Data.Nat.Properties.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_3866 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_3866
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_608
      (coe d_'42''45'isSemigroup_3864) erased
-- Data.Nat.Properties.*-1-isMonoid
d_'42''45'1'45'isMonoid_3868 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'1'45'isMonoid_3868
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe d_'42''45'isSemigroup_3864) (coe d_'42''45'identity_3810)
-- Data.Nat.Properties.*-1-isCommutativeMonoid
d_'42''45'1'45'isCommutativeMonoid_3870 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'1'45'isCommutativeMonoid_3870
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe d_'42''45'1'45'isMonoid_3868) erased
-- Data.Nat.Properties.+-*-isSemiring
d_'43''45''42''45'isSemiring_3872 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_'43''45''42''45'isSemiring_3872
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1740
      (coe
         MAlonzo.Code.Algebra.Structures.C_constructor_1630
         (coe d_'43''45'0'45'isCommutativeMonoid_3466) erased erased
         (coe d_'42''45'identity_3810) (coe d_'42''45'distrib'45''43'_3846))
      (coe d_'42''45'zero_3818)
-- Data.Nat.Properties.+-*-isCommutativeSemiring
d_'43''45''42''45'isCommutativeSemiring_3874 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_'43''45''42''45'isCommutativeSemiring_3874
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe d_'43''45''42''45'isSemiring_3872) erased
-- Data.Nat.Properties.*-magma
d_'42''45'magma_3876 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'42''45'magma_3876
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124 mulInt
      d_'42''45'isMagma_3862
-- Data.Nat.Properties.*-semigroup
d_'42''45'semigroup_3878 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'42''45'semigroup_3878
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614 mulInt
      d_'42''45'isSemigroup_3864
-- Data.Nat.Properties.*-commutativeSemigroup
d_'42''45'commutativeSemigroup_3880 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'42''45'commutativeSemigroup_3880
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_754 mulInt
      d_'42''45'isCommutativeSemigroup_3866
-- Data.Nat.Properties.*-1-monoid
d_'42''45'1'45'monoid_3882 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'42''45'1'45'monoid_3882
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990 mulInt
      (1 :: Integer) d_'42''45'1'45'isMonoid_3868
-- Data.Nat.Properties.*-1-commutativeMonoid
d_'42''45'1'45'commutativeMonoid_3884 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'42''45'1'45'commutativeMonoid_3884
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088 mulInt
      (1 :: Integer) d_'42''45'1'45'isCommutativeMonoid_3870
-- Data.Nat.Properties.+-*-semiring
d_'43''45''42''45'semiring_3886 ::
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2356
d_'43''45''42''45'semiring_3886
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2518 addInt mulInt
      (0 :: Integer) (1 :: Integer) d_'43''45''42''45'isSemiring_3872
-- Data.Nat.Properties.+-*-commutativeSemiring
d_'43''45''42''45'commutativeSemiring_3888 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
d_'43''45''42''45'commutativeSemiring_3888
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2706 addInt mulInt
      (0 :: Integer) (1 :: Integer)
      d_'43''45''42''45'isCommutativeSemiring_3874
-- Data.Nat.Properties.*-cancelʳ-≡
d_'42''45'cancel'691''45''8801'_3898 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'691''45''8801'_3898 = erased
-- Data.Nat.Properties.*-cancelˡ-≡
d_'42''45'cancel'737''45''8801'_3920 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45''8801'_3920 = erased
-- Data.Nat.Properties.m*n≡0⇒m≡0∨n≡0
d_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3940 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3940 v0 ~v1 ~v2
  = du_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3940 v0
du_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3940 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3940 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Nat.Properties.m*n≢0
d_m'42'n'8802'0_3958 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_m'42'n'8802'0_3958 ~v0 ~v1 ~v2 ~v3 = du_m'42'n'8802'0_3958
du_m'42'n'8802'0_3958 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_m'42'n'8802'0_3958
  = coe
      MAlonzo.Code.Data.Nat.Base.C_constructor_120
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Properties.m*n≢0⇒m≢0
d_m'42'n'8802'0'8658'm'8802'0_3968 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_m'42'n'8802'0'8658'm'8802'0_3968 ~v0 ~v1 ~v2
  = du_m'42'n'8802'0'8658'm'8802'0_3968
du_m'42'n'8802'0'8658'm'8802'0_3968 ::
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_m'42'n'8802'0'8658'm'8802'0_3968
  = coe
      MAlonzo.Code.Data.Nat.Base.C_constructor_120
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Properties.m*n≢0⇒n≢0
d_m'42'n'8802'0'8658'n'8802'0_3974 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_m'42'n'8802'0'8658'n'8802'0_3974 ~v0 ~v1 ~v2
  = du_m'42'n'8802'0'8658'n'8802'0_3974
du_m'42'n'8802'0'8658'n'8802'0_3974 ::
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_m'42'n'8802'0'8658'n'8802'0_3974
  = coe du_m'42'n'8802'0'8658'm'8802'0_3968
-- Data.Nat.Properties.m*n≡0⇒m≡0
d_m'42'n'8801'0'8658'm'8801'0_3990 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'8801'0'8658'm'8801'0_3990 = erased
-- Data.Nat.Properties.m*n≡1⇒m≡1
d_m'42'n'8801'1'8658'm'8801'1_3998 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'8801'1'8658'm'8801'1_3998 = erased
-- Data.Nat.Properties.m*n≡1⇒n≡1
d_m'42'n'8801'1'8658'n'8801'1_4012 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'8801'1'8658'n'8801'1_4012 = erased
-- Data.Nat.Properties.[m*n]*[o*p]≡[m*o]*[n*p]
d_'91'm'42'n'93''42''91'o'42'p'93''8801''91'm'42'o'93''42''91'n'42'p'93'_4028 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'42'n'93''42''91'o'42'p'93''8801''91'm'42'o'93''42''91'n'42'p'93'_4028
  = erased
-- Data.Nat.Properties.m≢0∧n>1⇒m*n>1
d_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_4152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_154 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_154
d_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_4152 ~v0 ~v1 ~v2 ~v3
  = du_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_4152
du_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_4152 ::
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_154
du_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_4152
  = coe
      MAlonzo.Code.Data.Nat.Base.C_constructor_162
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Properties.n≢0∧m>1⇒m*n>1
d_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4166 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_154 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_154
d_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4166 ~v0 ~v1 ~v2 ~v3
  = du_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4166
du_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4166 ::
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_154
du_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4166
  = coe du_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_4152
-- Data.Nat.Properties.*-cancelʳ-≤
d_'42''45'cancel'691''45''8804'_4184 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'cancel'691''45''8804'_4184 v0 ~v1 ~v2 ~v3 ~v4
  = du_'42''45'cancel'691''45''8804'_4184 v0
du_'42''45'cancel'691''45''8804'_4184 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'cancel'691''45''8804'_4184 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_'42''45'cancel'691''45''8804'_4184 (coe v1)))
-- Data.Nat.Properties.*-cancelˡ-≤
d_'42''45'cancel'737''45''8804'_4198 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'cancel'737''45''8804'_4198 v0 ~v1 ~v2 ~v3
  = du_'42''45'cancel'737''45''8804'_4198 v0
du_'42''45'cancel'737''45''8804'_4198 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'cancel'737''45''8804'_4198 v0 v1
  = coe du_'42''45'cancel'691''45''8804'_4184 (coe v0)
-- Data.Nat.Properties.*-mono-≤
d_'42''45'mono'45''8804'_4214 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'45''8804'_4214 ~v0 v1 ~v2 v3 v4 v5
  = du_'42''45'mono'45''8804'_4214 v1 v3 v4 v5
du_'42''45'mono'45''8804'_4214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'45''8804'_4214 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> let v7 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'43''45'mono'45''8804'_3672 (coe mulInt (coe v7) (coe v1))
                (coe v3)
                (coe
                   du_'42''45'mono'45''8804'_4214 (coe v7) (coe v1) (coe v6)
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.*-monoˡ-≤
d_'42''45'mono'737''45''8804'_4222 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'737''45''8804'_4222
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8322''8658'mono'691'_352
      (coe d_'8804''45'refl_2900)
      (\ v0 v1 v2 v3 v4 v5 ->
         coe du_'42''45'mono'45''8804'_4214 v1 v3 v4 v5)
-- Data.Nat.Properties.*-monoʳ-≤
d_'42''45'mono'691''45''8804'_4224 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'691''45''8804'_4224
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8322''8658'mono'737'_342
      (coe d_'8804''45'refl_2900)
      (\ v0 v1 v2 v3 v4 v5 ->
         coe du_'42''45'mono'45''8804'_4214 v1 v3 v4 v5)
-- Data.Nat.Properties.*-mono-<
d_'42''45'mono'45''60'_4226 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'45''60'_4226 ~v0 v1 ~v2 v3 v4 v5
  = du_'42''45'mono'45''60'_4226 v1 v3 v4 v5
du_'42''45'mono'45''60'_4226 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'45''60'_4226 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> case coe v6 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe seq (coe v3) (coe du_0'60'1'43'n_3216)
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12
                      -> coe
                           du_'43''45'mono'45''60'_3706
                           (mulInt (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1))
                           (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12)
                           (coe
                              du_'42''45'mono'45''60'_4226
                              (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1)
                              (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)
                              (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.*-monoˡ-<
d_'42''45'mono'737''45''60'_4240 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'737''45''60'_4240 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60'_4240 v0 v2 v3 v4
du_'42''45'mono'737''45''60'_4240 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'737''45''60'_4240 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> case coe v6 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26 -> coe du_0'60'1'43'n_3216
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
               -> let v10 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_'43''45'mono'45''8804''45''60'_3696
                       (coe
                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                          (\ v11 v12 -> v12) (\ v11 -> mulInt (coe v11) (coe v0)) v10
                          (subInt (coe v2) (coe (1 :: Integer))))
                       (coe d_'8804''45'refl_2900 (coe v0))
                       (coe
                          du_'42''45'mono'737''45''60'_4240 (coe v0) (coe v10)
                          (coe subInt (coe v2) (coe (1 :: Integer)))
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.*-monoʳ-<
d_'42''45'mono'691''45''60'_4254 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'691''45''60'_4254 v0 ~v1 ~v2 v3 v4
  = du_'42''45'mono'691''45''60'_4254 v0 v3 v4
du_'42''45'mono'691''45''60'_4254 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'691''45''60'_4254 v0 v1 v2
  = case coe v0 of
      1 -> case coe v2 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
               -> coe
                    du_'43''45'mono'45''8804'_3672 (coe (0 :: Integer))
                    (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
                    (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v2 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
               -> coe
                    du_'43''45'mono'45''8804'_3672
                    (coe mulInt (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1))
                    (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
                    (coe
                       du_'60''8658''8804'_2998
                       (coe
                          du_'42''45'mono'691''45''60'_4254
                          (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1)
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.m≤m*n
d_m'8804'm'42'n_4268 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'm'42'n_4268 v0 v1 ~v2 = du_m'8804'm'42'n_4268 v0 v1
du_m'8804'm'42'n_4268 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'm'42'n_4268 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2950)
         (\ v2 v3 v4 -> coe du_'60''8658''8804'_2998 v4))
      v0 (mulInt (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
         (\ v2 v3 v4 v5 v6 -> v6) v0 (mulInt (coe v0) (coe (1 :: Integer)))
         (mulInt (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_2950)
               (\ v2 v3 v4 v5 v6 -> coe du_'8804''45''60''45'trans_3128 v5 v6))
            (mulInt (coe v0) (coe (1 :: Integer))) (mulInt (coe v0) (coe v1))
            (mulInt (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2950))
               (coe mulInt (coe v0) (coe v1)))
            (coe
               d_'42''45'mono'691''45''8804'_4224 v0 (1 :: Integer) v1
               (coe du_0'60'1'43'n_3216)))
         erased)
-- Data.Nat.Properties.m≤n*m
d_m'8804'n'42'm_4280 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'42'm_4280 v0 v1 ~v2 = du_m'8804'n'42'm_4280 v0 v1
du_m'8804'n'42'm_4280 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'42'm_4280 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2950)
         (\ v2 v3 v4 -> coe du_'60''8658''8804'_2998 v4))
      v0 (mulInt (coe v1) (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_2950)
            (\ v2 v3 v4 v5 v6 -> coe du_'8804''45''60''45'trans_3128 v5 v6))
         v0 (mulInt (coe v0) (coe v1)) (mulInt (coe v1) (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
            (\ v2 v3 v4 v5 v6 -> v6) (mulInt (coe v0) (coe v1))
            (mulInt (coe v1) (coe v0)) (mulInt (coe v1) (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2950))
               (coe mulInt (coe v1) (coe v0)))
            erased)
         (coe du_m'8804'm'42'n_4268 (coe v0) (coe v1)))
-- Data.Nat.Properties.m≤n⇒m≤o*n
d_m'8804'n'8658'm'8804'o'42'n_4290 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'm'8804'o'42'n_4290 ~v0 v1 v2 ~v3 v4
  = du_m'8804'n'8658'm'8804'o'42'n_4290 v1 v2 v4
du_m'8804'n'8658'm'8804'o'42'n_4290 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'm'8804'o'42'n_4290 v0 v1 v2
  = coe
      du_'8804''45'trans_2908 (coe v2)
      (coe du_m'8804'n'42'm_4280 (coe v0) (coe v1))
-- Data.Nat.Properties.m≤n⇒m≤n*o
d_m'8804'n'8658'm'8804'n'42'o_4300 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'm'8804'n'42'o_4300 ~v0 v1 v2 ~v3 v4
  = du_m'8804'n'8658'm'8804'n'42'o_4300 v1 v2 v4
du_m'8804'n'8658'm'8804'n'42'o_4300 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'm'8804'n'42'o_4300 v0 v1 v2
  = coe
      du_'8804''45'trans_2908 (coe v2)
      (coe du_m'8804'm'42'n_4268 (coe v0) (coe v1))
-- Data.Nat.Properties.m<m*n
d_m'60'm'42'n_4312 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'm'42'n_4312 v0 v1 ~v2 v3 = du_m'60'm'42'n_4312 v0 v1 v3
du_m'60'm'42'n_4312 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'm'42'n_4312 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
           -> coe
                seq (coe v6)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                   (coe v0) (coe mulInt (coe v0) (coe v1))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                         (\ v7 v8 v9 v10 v11 -> coe du_'60''45'trans_3122 v8 v10 v11)
                         (coe
                            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                         (\ v7 v8 v9 v10 v11 ->
                            coe du_'60''45''8804''45'trans_3134 v10 v11))
                      v0 (addInt (coe v1) (coe v3)) (mulInt (coe v0) (coe v1))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe d_'8804''45'isPreorder_2950)
                            (\ v7 v8 v9 v10 v11 ->
                               coe du_'8804''45''60''45'trans_3128 v10 v11))
                         (addInt (coe v1) (coe v3))
                         (addInt (coe v1) (coe mulInt (coe v3) (coe v1)))
                         (mulInt (coe v0) (coe v1))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe d_'8804''45'isPreorder_2950))
                            (coe mulInt (coe v0) (coe v1)))
                         (coe
                            d_'43''45'mono'691''45''8804'_3684 v1 v3 (mulInt (coe v3) (coe v1))
                            (coe du_m'8804'm'42'n_4268 (coe v3) (coe v1))))
                      (coe
                         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                         (coe
                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                            (coe du_m'8804'n'43'm_3636 (coe v3))))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m<n⇒m<n*o
d_m'60'n'8658'm'60'n'42'o_4326 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'n'42'o_4326 ~v0 v1
  = du_m'60'n'8658'm'60'n'42'o_4326 v1
du_m'60'n'8658'm'60'n'42'o_4326 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'60'n'42'o_4326 v0 v1 v2 v3
  = coe du_m'8804'n'8658'm'8804'n'42'o_4300 (coe v0) v1 v3
-- Data.Nat.Properties.m<n⇒m<o*n
d_m'60'n'8658'm'60'o'42'n_4336 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'o'42'n_4336 ~v0 v1
  = du_m'60'n'8658'm'60'o'42'n_4336 v1
du_m'60'n'8658'm'60'o'42'n_4336 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'60'o'42'n_4336 v0 v1 v2 v3
  = coe du_m'8804'n'8658'm'8804'o'42'n_4290 (coe v0) v1 v3
-- Data.Nat.Properties.*-cancelʳ-<
d_'42''45'cancel'691''45''60'_4338 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'cancel'691''45''60'_4338 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''60'_4338 v0 v1 v2
du_'42''45'cancel'691''45''60'_4338 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'cancel'691''45''60'_4338 v0 v1 v2
  = let v3
          = let v3 = subInt (coe v1) (coe (1 :: Integer)) in
            coe
              (let v4 = subInt (coe v2) (coe (1 :: Integer)) in
               coe
                 (coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       du_'42''45'cancel'691''45''60'_4338 (coe v0) (coe v3)
                       (coe v4)))) in
    coe
      (coe
         seq (coe v0)
         (case coe v1 of
            0 -> case coe v2 of
                   _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                       coe du_0'60'1'43'n_3216
                   _ -> coe v3
            _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                 coe
                   (case coe v2 of
                      _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                          let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                          coe
                            (coe
                               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                               (coe
                                  du_'42''45'cancel'691''45''60'_4338 (coe v0) (coe v4) (coe v5)))
                      _ -> coe v3)))
-- Data.Nat.Properties.*-cancelˡ-<
d_'42''45'cancel'737''45''60'_4354 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'cancel'737''45''60'_4354 v0 v1 v2 v3
  = coe
      du_'42''45'cancel'691''45''60'_4338 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Properties.*-cancel-<
d_'42''45'cancel'45''60'_4370 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'cancel'45''60'_4370
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_'42''45'cancel'737''45''60'_4354)
      (\ v0 v1 v2 v3 -> coe du_'42''45'cancel'691''45''60'_4338 v0 v1 v2)
-- Data.Nat.Properties.^-identityʳ
d_'94''45'identity'691'_4372 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'identity'691'_4372 = erased
-- Data.Nat.Properties.^-zeroˡ
d_'94''45'zero'737'_4376 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'zero'737'_4376 = erased
-- Data.Nat.Properties.^-distribˡ-+-*
d_'94''45'distrib'737''45''43''45''42'_4386 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'distrib'737''45''43''45''42'_4386 = erased
-- Data.Nat.Properties.^-semigroup-morphism
d_'94''45'semigroup'45'morphism_4404 ::
  Integer -> MAlonzo.Code.Algebra.Morphism.T_IsSemigroupMorphism_148
d_'94''45'semigroup'45'morphism_4404 ~v0
  = du_'94''45'semigroup'45'morphism_4404
du_'94''45'semigroup'45'morphism_4404 ::
  MAlonzo.Code.Algebra.Morphism.T_IsSemigroupMorphism_148
du_'94''45'semigroup'45'morphism_4404
  = coe MAlonzo.Code.Algebra.Morphism.C_constructor_160 erased erased
-- Data.Nat.Properties.^-monoid-morphism
d_'94''45'monoid'45'morphism_4412 ::
  Integer -> MAlonzo.Code.Algebra.Morphism.T_IsMonoidMorphism_308
d_'94''45'monoid'45'morphism_4412 ~v0
  = du_'94''45'monoid'45'morphism_4412
du_'94''45'monoid'45'morphism_4412 ::
  MAlonzo.Code.Algebra.Morphism.T_IsMonoidMorphism_308
du_'94''45'monoid'45'morphism_4412
  = coe
      MAlonzo.Code.Algebra.Morphism.C_constructor_326
      (coe du_'94''45'semigroup'45'morphism_4404) erased
-- Data.Nat.Properties.^-*-assoc
d_'94''45''42''45'assoc_4420 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45''42''45'assoc_4420 = erased
-- Data.Nat.Properties.m^n≡0⇒m≡0
d_m'94'n'8801'0'8658'm'8801'0_4442 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'94'n'8801'0'8658'm'8801'0_4442 = erased
-- Data.Nat.Properties.m^n≡1⇒n≡0∨m≡1
d_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4454 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4454 ~v0 v1 ~v2
  = du_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4454 v1
du_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4454 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4454 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Nat.Properties.m^n≢0
d_m'94'n'8802'0_4470 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_m'94'n'8802'0_4470 v0 v1 ~v2 = du_m'94'n'8802'0_4470 v0 v1
du_m'94'n'8802'0_4470 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_m'94'n'8802'0_4470 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'8802''45'nonZero_128
      (coe MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe v0) (coe v1))
-- Data.Nat.Properties.m^n>0
d_m'94'n'62'0_4482 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'94'n'62'0_4482 ~v0 ~v1 ~v2 = du_m'94'n'62'0_4482
du_m'94'n'62'0_4482 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'94'n'62'0_4482
  = coe MAlonzo.Code.Data.Nat.Base.du_'62''45'nonZero'8315''185'_148
-- Data.Nat.Properties.^-monoˡ-≤
d_'94''45'mono'737''45''8804'_4488 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'94''45'mono'737''45''8804'_4488 v0 ~v1 v2 v3
  = du_'94''45'mono'737''45''8804'_4488 v0 v2 v3
du_'94''45'mono'737''45''8804'_4488 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'94''45'mono'737''45''8804'_4488 v0 v1 v2
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'42''45'mono'45''8804'_4214 (coe v1)
                (coe MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe v1) (coe v3))
                (coe v2)
                (coe
                   du_'94''45'mono'737''45''8804'_4488 (coe v3) (coe v1) (coe v2)))
-- Data.Nat.Properties.^-monoʳ-≤
d_'94''45'mono'691''45''8804'_4502 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'94''45'mono'691''45''8804'_4502 v0 ~v1 v2 v3 v4
  = du_'94''45'mono'691''45''8804'_4502 v0 v2 v3 v4
du_'94''45'mono'691''45''8804'_4502 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'94''45'mono'691''45''8804'_4502 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             du_n'8802'0'8658'n'62'0_3232
             (coe MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe v0) (coe v2))
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> let v7 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v8 = subInt (coe v2) (coe (1 :: Integer)) in
              coe
                (coe
                   d_'42''45'mono'691''45''8804'_4224 v0
                   (coe
                      MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                      (MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe v0)) (\ v9 v10 -> v9)
                      v7 v8)
                   (coe
                      MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                      (\ v9 v10 -> v10)
                      (MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe v0)) v7 v8)
                   (coe
                      du_'94''45'mono'691''45''8804'_4502 (coe v0) (coe v7) (coe v8)
                      (coe v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.^-monoˡ-<
d_'94''45'mono'737''45''60'_4518 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'94''45'mono'737''45''60'_4518 v0 ~v1 v2 v3 v4
  = du_'94''45'mono'737''45''60'_4518 v0 v2 v3 v4
du_'94''45'mono'737''45''60'_4518 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'94''45'mono'737''45''60'_4518 v0 v1 v2 v3
  = case coe v0 of
      1 -> coe
             du_'42''45'mono'737''45''60'_4240 (coe (1 :: Integer)) (coe v1)
             (coe v2) (coe v3)
      _ -> coe
             du_'42''45'mono'45''60'_4226 (coe v2)
             (coe
                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                (\ v4 v5 -> v5)
                (\ v4 ->
                   MAlonzo.Code.Data.Nat.Base.d__'94'__276
                     (coe v4) (coe subInt (coe v0) (coe (1 :: Integer))))
                v1 v2)
             (coe v3)
             (coe
                du_'94''45'mono'737''45''60'_4518
                (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1) (coe v2)
                (coe v3))
-- Data.Nat.Properties.^-monoʳ-<
d_'94''45'mono'691''45''60'_4530 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'94''45'mono'691''45''60'_4530 v0 v1 v2 v3 v4
  = case coe v2 of
      0 -> let v5 = subInt (coe v3) (coe (1 :: Integer)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                  -> coe
                       seq (coe v8)
                       (coe
                          du_'42''45'mono'45''8804'_4214 (coe v0)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe v0) (coe v5))
                          (coe v1) (coe du_m'94'n'62'0_4482))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v6 = subInt (coe v3) (coe (1 :: Integer)) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                     -> coe
                          du_'42''45'mono'691''45''60'_4254 (coe v0)
                          (coe
                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                             (\ v10 v11 -> v11)
                             (MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe v0)) v5 v6)
                          (coe
                             d_'94''45'mono'691''45''60'_4530 (coe v0) (coe v1) (coe v5)
                             (coe v6) (coe v9))
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Nat.Properties.m≤n⇒m⊔n≡n
d_m'8804'n'8658'm'8852'n'8801'n_4548 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8852'n'8801'n_4548 = erased
-- Data.Nat.Properties.m≥n⇒m⊔n≡m
d_m'8805'n'8658'm'8852'n'8801'm_4554 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8805'n'8658'm'8852'n'8801'm_4554 = erased
-- Data.Nat.Properties.m≤n⇒m⊓n≡m
d_m'8804'n'8658'm'8851'n'8801'm_4564 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8851'n'8801'm_4564 = erased
-- Data.Nat.Properties.m≥n⇒m⊓n≡n
d_m'8805'n'8658'm'8851'n'8801'n_4570 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8805'n'8658'm'8851'n'8801'n_4570 = erased
-- Data.Nat.Properties.⊓-operator
d_'8851''45'operator_4580 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106
d_'8851''45'operator_4580
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_constructor_136
      (coe MAlonzo.Code.Data.Nat.Base.d__'8851'__236) erased erased
-- Data.Nat.Properties.⊔-operator
d_'8852''45'operator_4582 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138
d_'8852''45'operator_4582
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_constructor_168
      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208) erased erased
-- Data.Nat.Properties.⊔≡⊔′
d_'8852''8801''8852''8242'_4588 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''8801''8852''8242'_4588 = erased
-- Data.Nat.Properties.⊓≡⊓′
d_'8851''8801''8851''8242'_4614 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''8801''8851''8242'_4614 = erased
-- Data.Nat.Properties.⊓-⊔-properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_4638 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8851'_4638 = erased
-- Data.Nat.Properties.⊓-⊔-properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_4640 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8852'_4640 = erased
-- Data.Nat.Properties.⊓-⊔-properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_4642 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8851'_4642 = erased
-- Data.Nat.Properties.⊓-⊔-properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_4644 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8852'_4644 = erased
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_4646 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'x_4646
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_4648 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8658'x'8851'z'8804'y_4648
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3276
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_4650 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8658'z'8851'x'8804'y_4650
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3288
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_4652 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8658'x'8851'z'8804'y_4652
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3276
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_4654 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8658'z'8851'x'8804'y_4654
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3288
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_4656 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8851'z'8658'x'8804'y_4656
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3300
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_4658 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8851'z'8658'x'8804'z_4658
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3314
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_4660 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'y_4660
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_4662 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8776'x'8658'x'8804'y_4662
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_4664 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8776'y'8658'y'8804'x_4664
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_4666 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'x_4666
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤x⊔y
d_x'8851'y'8804'x'8852'y_4668 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'x'8852'y_4668
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_x'8851'y'8804'x'8852'y_3440
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_4670 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'y_4670
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_4672 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8776'x'8658'x'8804'y_4672
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_4674 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8776'y'8658'y'8804'x_4674
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_4676 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8851'z'8658'x'8804'y_4676
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3300
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_4678 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8851'z'8658'x'8804'z_4678
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3314
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-absorbs-⊔
d_'8851''45'absorbs'45''8852'_4680 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'absorbs'45''8852'_4680 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_4682 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_4682 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_4684 :: MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8851''45'band_4684
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3168
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_4686 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_4686 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_4688 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'8851''45'commutativeSemigroup_4688
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3170
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-cong
d_'8851''45'cong_4690 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong_4690 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-congʳ
d_'8851''45'cong'691'_4692 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong'691'_4692 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-congˡ
d_'8851''45'cong'737'_4694 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong'737'_4694 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-distrib-⊔
d_'8851''45'distrib'45''8852'_4696 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'distrib'45''8852'_4696
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3260
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-properties.⊓-distribʳ-⊔
d_'8851''45'distrib'691''45''8852'_4698 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'691''45''8852'_4698 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-distribˡ-⊔
d_'8851''45'distrib'737''45''8852'_4700 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'737''45''8852'_4700 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_4702 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'glb_4702
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_4704 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_4704 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-identity
d_'8851''45'identity_4706 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_4706 ~v0 ~v1 = du_'8851''45'identity_4706
du_'8851''45'identity_4706 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'identity_4706
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-identityʳ
d_'8851''45'identity'691'_4708 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'identity'691'_4708 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-identityˡ
d_'8851''45'identity'737'_4710 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'identity'737'_4710 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_4712 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8851''45'isBand_4712
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3150
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_4714 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'8851''45'isCommutativeSemigroup_4714
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3152
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_4716 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8851''45'isMagma_4716
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3146
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isMonoid
d_'8851''45'isMonoid_4718 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8851''45'isMonoid_4718
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3158
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_4720 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_'8851''45'isSelectiveMagma_4720
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_4722 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8851''45'isSemigroup_4722
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3148
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_4724 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8851''45'magma_4724
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3164
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_4726 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'45''8804'_4726
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoid
d_'8851''45'monoid_4728 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8851''45'monoid_4728
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3176
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_4730 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'691''45''8804'_4730
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_4732 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'737''45''8804'_4732
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3372
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-rawMagma
d_'8851''45'rawMagma_4734 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8851''45'rawMagma_4734
  = let v0 = d_'8851''45'operator_4580 in
    coe
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'rawMagma_3162
         (coe v0))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_4736 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_4736
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_4738 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
d_'8851''45'selectiveMagma_4738
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3172
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_4740 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8851''45'semigroup_4740
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3166
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_4742 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_4742 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-zero
d_'8851''45'zero_4744 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_4744 ~v0 ~v1 = du_'8851''45'zero_4744
du_'8851''45'zero_4744 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8851''45'zero_4744
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-zeroʳ
d_'8851''45'zero'691'_4746 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'691'_4746 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-zeroˡ
d_'8851''45'zero'737'_4748 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'737'_4748 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-⊔-absorptive
d_'8851''45''8852''45'absorptive_4750 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45''8852''45'absorptive_4750
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'absorptive_3340
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-properties.⊔-absorbs-⊓
d_'8852''45'absorbs'45''8851'_4752 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'absorbs'45''8851'_4752 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_4754 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_4754 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_4756 :: MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8851''45'band_4756
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3168
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_4758 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_4758 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_4760 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'8851''45'commutativeSemigroup_4760
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3170
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-cong
d_'8851''45'cong_4762 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong_4762 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-congʳ
d_'8851''45'cong'691'_4764 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong'691'_4764 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-congˡ
d_'8851''45'cong'737'_4766 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'cong'737'_4766 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊔-distrib-⊓
d_'8852''45'distrib'45''8851'_4768 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'distrib'45''8851'_4768
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'45''8851'_3292
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-properties.⊔-distribʳ-⊓
d_'8852''45'distrib'691''45''8851'_4770 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'691''45''8851'_4770 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊔-distribˡ-⊓
d_'8852''45'distrib'737''45''8851'_4772 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'737''45''8851'_4772 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_4774 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_4774 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-identity
d_'8851''45'identity_4776 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_4776
  = let v0 = d_'8852''45'operator_4582 in
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
-- Data.Nat.Properties.⊓-⊔-properties.⊓-identityʳ
d_'8851''45'identity'691'_4778 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'identity'691'_4778 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-identityˡ
d_'8851''45'identity'737'_4780 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'identity'737'_4780 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_4782 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8851''45'isBand_4782
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3150
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_4784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'8851''45'isCommutativeSemigroup_4784
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3152
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_4786 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8851''45'isMagma_4786
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3146
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isMonoid
d_'8851''45'isMonoid_4788 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8851''45'isMonoid_4788
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMonoid_3158
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_4790 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_'8851''45'isSelectiveMagma_4790
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3154
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_4792 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8851''45'isSemigroup_4792
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3148
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_4794 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'glb_4794
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_4796 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8851''45'magma_4796
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3164
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_4798 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'45''8804'_4798
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoid
d_'8851''45'monoid_4800 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8851''45'monoid_4800
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'monoid_3176
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_4802 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'691''45''8804'_4802
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3382
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_4804 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'737''45''8804'_4804
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3372
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_4806 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_4806
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3104
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_4808 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
d_'8851''45'selectiveMagma_4808
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3172
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_4810 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8851''45'semigroup_4810
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3166
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_4812 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_4812 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-zero
d_'8851''45'zero_4814 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_4814
  = let v0 = d_'8852''45'operator_4582 in
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
-- Data.Nat.Properties.⊓-⊔-properties.⊓-zeroʳ
d_'8851''45'zero'691'_4816 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'691'_4816 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-zeroˡ
d_'8851''45'zero'737'_4818 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'737'_4818 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊔-⊓-absorptive
d_'8852''45''8851''45'absorptive_4820 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45''8851''45'absorptive_4820
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'absorptive_3338
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_4824 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8851''45'isSemilattice_4824
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_616
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_4826 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_4826
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8851''45'operator_4580 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_618
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-⊔-distributiveLattice
d_'8851''45''8852''45'distributiveLattice_4828 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
d_'8851''45''8852''45'distributiveLattice_4828
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'distributiveLattice_822
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-⊔-isDistributiveLattice
d_'8851''45''8852''45'isDistributiveLattice_4830 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_'8851''45''8852''45'isDistributiveLattice_4830
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isDistributiveLattice_812
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-⊔-isLattice
d_'8851''45''8852''45'isLattice_4832 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8851''45''8852''45'isLattice_4832
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isLattice_810
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-⊔-lattice
d_'8851''45''8852''45'lattice_4834 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8851''45''8852''45'lattice_4834
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'lattice_818
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_4836 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8851''45'isSemilattice_4836
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_616
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_4838 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_4838
  = let v0 = d_'8804''45'totalPreorder_2962 in
    coe
      (let v1 = d_'8852''45'operator_4582 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_618
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊔-⊓-distributiveLattice
d_'8852''45''8851''45'distributiveLattice_4840 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
d_'8852''45''8851''45'distributiveLattice_4840
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'distributiveLattice_820
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊔-⊓-isDistributiveLattice
d_'8852''45''8851''45'isDistributiveLattice_4842 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_'8852''45''8851''45'isDistributiveLattice_4842
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isDistributiveLattice_814
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊔-⊓-isLattice
d_'8852''45''8851''45'isLattice_4844 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8852''45''8851''45'isLattice_4844
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isLattice_808
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊔-⊓-lattice
d_'8852''45''8851''45'lattice_4846 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8852''45''8851''45'lattice_4846
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'lattice_816
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582)
-- Data.Nat.Properties.⊔-identityˡ
d_'8852''45'identity'737'_4848 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'identity'737'_4848 = erased
-- Data.Nat.Properties.⊔-identityʳ
d_'8852''45'identity'691'_4850 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'identity'691'_4850 = erased
-- Data.Nat.Properties.⊔-identity
d_'8852''45'identity_4854 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'identity_4854
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.⊔-0-isMonoid
d_'8852''45'0'45'isMonoid_4856 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8852''45'0'45'isMonoid_4856
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3148
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe d_'8804''45'totalPreorder_2962))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe d_'8852''45'operator_4582)))
      (coe d_'8852''45'identity_4854)
-- Data.Nat.Properties.⊔-0-isCommutativeMonoid
d_'8852''45'0'45'isCommutativeMonoid_4858 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'8852''45'0'45'isCommutativeMonoid_4858
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe d_'8852''45'0'45'isMonoid_4856)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe d_'8804''45'totalPreorder_2962))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe d_'8852''45'operator_4582)))
-- Data.Nat.Properties.⊔-0-monoid
d_'8852''45'0'45'monoid_4860 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8852''45'0'45'monoid_4860
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990
      MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (0 :: Integer)
      d_'8852''45'0'45'isMonoid_4856
-- Data.Nat.Properties.⊔-0-commutativeMonoid
d_'8852''45'0'45'commutativeMonoid_4862 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'8852''45'0'45'commutativeMonoid_4862
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088
      MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (0 :: Integer)
      d_'8852''45'0'45'isCommutativeMonoid_4858
-- Data.Nat.Properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_4870 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8852'_4870 = erased
-- Data.Nat.Properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_4880 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8851'_4880 = erased
-- Data.Nat.Properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_4890 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8851'_4890 = erased
-- Data.Nat.Properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_4900 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8852'_4900 = erased
-- Data.Nat.Properties.m<n⇒m<n⊔o
d_m'60'n'8658'm'60'n'8852'o_4906 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'n'8852'o_4906 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3276
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_4582))
      (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.m<n⇒m<o⊔n
d_m'60'n'8658'm'60'o'8852'n_4910 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'o'8852'n_4910 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3288
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_4582))
      (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.m⊔n<o⇒m<o
d_m'8852'n'60'o'8658'm'60'o_4918 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8852'n'60'o'8658'm'60'o_4918 v0 v1 ~v2 v3
  = du_m'8852'n'60'o'8658'm'60'o_4918 v0 v1 v3
du_m'8852'n'60'o'8658'm'60'o_4918 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8852'n'60'o'8658'm'60'o_4918 v0 v1 v2
  = coe
      du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe d_'8804''45'totalPreorder_2962))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe d_'8852''45'operator_4582))
         (coe v0) (coe v1))
      (coe v2)
-- Data.Nat.Properties.m⊔n<o⇒n<o
d_m'8852'n'60'o'8658'n'60'o_4932 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8852'n'60'o'8658'n'60'o_4932 v0 v1 ~v2 v3
  = du_m'8852'n'60'o'8658'n'60'o_4932 v0 v1 v3
du_m'8852'n'60'o'8658'n'60'o_4932 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8852'n'60'o'8658'n'60'o_4932 v0 v1 v2
  = coe
      du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe d_'8804''45'totalPreorder_2962))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe d_'8852''45'operator_4582))
         (coe v0) (coe v1))
      (coe v2)
-- Data.Nat.Properties.⊔-mono-<
d_'8852''45'mono'45''60'_4940 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8852''45'mono'45''60'_4940 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_4582))
      (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3)
      (coe addInt (coe (1 :: Integer)) (coe v2))
-- Data.Nat.Properties.⊔-pres-<m
d_'8852''45'pres'45''60'm_4942 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8852''45'pres'45''60'm_4942 v0 v1 v2 v3 v4
  = coe d_'8852''45'mono'45''60'_4940 v0 v1 v2 v1 v3 v4
-- Data.Nat.Properties.+-distribˡ-⊔
d_'43''45'distrib'737''45''8852'_4952 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'737''45''8852'_4952 = erased
-- Data.Nat.Properties.+-distribʳ-⊔
d_'43''45'distrib'691''45''8852'_4964 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'691''45''8852'_4964 = erased
-- Data.Nat.Properties.+-distrib-⊔
d_'43''45'distrib'45''8852'_4966 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'distrib'45''8852'_4966
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.m⊔n≤m+n
d_m'8852'n'8804'm'43'n_4972 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8852'n'8804'm'43'n_4972 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
              (coe
                 (\ v2 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased))
              (coe
                 (\ v2 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased))
              (let v2
                     = coe
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                         (\ v2 -> coe du_'8804''7495''8658''8804'_2854 (coe v1))
                         (coe du_'8804''8658''8804''7495'_2866)
                         (coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                            (coe
                               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v1) (coe v0))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                               (coe
                                  MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v1)
                                  (coe v0)))) in
               coe
                 (case coe v2 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                      -> if coe v3
                           then coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v4))
                           else coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                  (coe du_'8816''8658''8805'_2880 (coe v1) (coe v0))
                    _ -> MAlonzo.RTE.mazUnreachableError)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
           -> coe du_m'8804'm'43'n_3624 (coe v0)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> coe du_m'8804'n'43'm_3636 (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.*-distribˡ-⊔
d_'42''45'distrib'737''45''8852'_5002 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8852'_5002 = erased
-- Data.Nat.Properties.*-distribʳ-⊔
d_'42''45'distrib'691''45''8852'_5024 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8852'_5024 = erased
-- Data.Nat.Properties.*-distrib-⊔
d_'42''45'distrib'45''8852'_5026 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''8852'_5026
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.⊓-zeroˡ
d_'8851''45'zero'737'_5028 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'737'_5028 = erased
-- Data.Nat.Properties.⊓-zeroʳ
d_'8851''45'zero'691'_5030 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'691'_5030 = erased
-- Data.Nat.Properties.⊓-zero
d_'8851''45'zero_5034 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_5034
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.⊔-⊓-isSemiringWithoutOne
d_'8852''45''8851''45'isSemiringWithoutOne_5036 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_'8852''45''8851''45'isSemiringWithoutOne_5036
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1430
      (coe d_'8852''45'0'45'isCommutativeMonoid_4858) erased
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_3060
         (coe d_'8804''45'totalPreorder_2962)
         (coe d_'8851''45'operator_4580))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3260
         (coe d_'8804''45'totalPreorder_2962)
         (coe d_'8851''45'operator_4580) (coe d_'8852''45'operator_4582))
      (coe d_'8851''45'zero_5034)
-- Data.Nat.Properties.⊔-⊓-isCommutativeSemiringWithoutOne
d_'8852''45''8851''45'isCommutativeSemiringWithoutOne_5038 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_'8852''45''8851''45'isCommutativeSemiringWithoutOne_5038
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1526
      (coe d_'8852''45''8851''45'isSemiringWithoutOne_5036)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
         (coe d_'8804''45'totalPreorder_2962)
         (coe d_'8851''45'operator_4580))
-- Data.Nat.Properties.⊔-⊓-commutativeSemiringWithoutOne
d_'8852''45''8851''45'commutativeSemiringWithoutOne_5040 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiringWithoutOne_2064
d_'8852''45''8851''45'commutativeSemiringWithoutOne_5040
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2198
      MAlonzo.Code.Data.Nat.Base.d__'8852'__208
      MAlonzo.Code.Data.Nat.Base.d__'8851'__236 (0 :: Integer)
      d_'8852''45''8851''45'isCommutativeSemiringWithoutOne_5038
-- Data.Nat.Properties.m<n⇒m⊓o<n
d_m'60'n'8658'm'8851'o'60'n_5044 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'8851'o'60'n_5044 v0 ~v1 v2 v3
  = du_m'60'n'8658'm'8851'o'60'n_5044 v0 v2 v3
du_m'60'n'8658'm'8851'o'60'n_5044 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'8851'o'60'n_5044 v0 v1 v2
  = coe
      du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
         (coe d_'8804''45'totalPreorder_2962)
         (coe d_'8851''45'operator_4580) (coe v0) (coe v1))
      (coe v2)
-- Data.Nat.Properties.m<n⇒o⊓m<n
d_m'60'n'8658'o'8851'm'60'n_5052 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'o'8851'm'60'n_5052 v0 ~v1 v2 v3
  = du_m'60'n'8658'o'8851'm'60'n_5052 v0 v2 v3
du_m'60'n'8658'o'8851'm'60'n_5052 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'o'8851'm'60'n_5052 v0 v1 v2
  = coe
      du_'8804''45''60''45'trans_3128
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
         (coe d_'8804''45'totalPreorder_2962)
         (coe d_'8851''45'operator_4580) (coe v1) (coe v0))
      (coe v2)
-- Data.Nat.Properties.m<n⊓o⇒m<n
d_m'60'n'8851'o'8658'm'60'n_5062 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8851'o'8658'm'60'n_5062 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3300
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580)
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.m<n⊓o⇒m<o
d_m'60'n'8851'o'8658'm'60'o_5068 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8851'o'8658'm'60'o_5068 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3314
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580)
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.⊓-mono-<
d_'8851''45'mono'45''60'_5070 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'45''60'_5070 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3322
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580)
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
      (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v3)
-- Data.Nat.Properties.⊓-pres-m<
d_'8851''45'pres'45'm'60'_5072 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'pres'45'm'60'_5072 v0 v1 v2 v3 v4
  = coe d_'8851''45'mono'45''60'_5070 v0 v1 v0 v2 v3 v4
-- Data.Nat.Properties.+-distribˡ-⊓
d_'43''45'distrib'737''45''8851'_5082 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'737''45''8851'_5082 = erased
-- Data.Nat.Properties.+-distribʳ-⊓
d_'43''45'distrib'691''45''8851'_5094 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'691''45''8851'_5094 = erased
-- Data.Nat.Properties.+-distrib-⊓
d_'43''45'distrib'45''8851'_5096 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'distrib'45''8851'_5096
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.m⊓n≤m+n
d_m'8851'n'8804'm'43'n_5102 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8851'n'8804'm'43'n_5102 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
              (coe
                 (\ v2 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased))
              (coe
                 (\ v2 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased))
              (let v2
                     = coe
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                         (\ v2 -> coe du_'8804''7495''8658''8804'_2854 (coe v0))
                         (coe du_'8804''8658''8804''7495'_2866)
                         (coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                            (coe
                               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0) (coe v1))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                               (coe
                                  MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
                                  (coe v1)))) in
               coe
                 (case coe v2 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                      -> if coe v3
                           then coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v4))
                           else coe
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                  (coe du_'8816''8658''8805'_2880 (coe v0) (coe v1))
                    _ -> MAlonzo.RTE.mazUnreachableError)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
           -> coe du_m'8804'm'43'n_3624 (coe v0)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> coe du_m'8804'n'43'm_3636 (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.*-distribˡ-⊓
d_'42''45'distrib'737''45''8851'_5132 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8851'_5132 = erased
-- Data.Nat.Properties.*-distribʳ-⊓
d_'42''45'distrib'691''45''8851'_5154 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8851'_5154 = erased
-- Data.Nat.Properties.*-distrib-⊓
d_'42''45'distrib'45''8851'_5156 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''8851'_5156
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.0∸n≡0
d_0'8760'n'8801'0_5158 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8760'n'8801'0_5158 = erased
-- Data.Nat.Properties.n∸n≡0
d_n'8760'n'8801'0_5162 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8760'n'8801'0_5162 = erased
-- Data.Nat.Properties.pred[m∸n]≡m∸[1+n]
d_pred'91'm'8760'n'93''8801'm'8760''91'1'43'n'93'_5170 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'91'm'8760'n'93''8801'm'8760''91'1'43'n'93'_5170 = erased
-- Data.Nat.Properties.m∸n≤m
d_m'8760'n'8804'm_5184 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'8804'm_5184 v0 v1
  = case coe v1 of
      0 -> coe
             d_'8804''45'refl_2900
             (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (0 :: Integer))
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe
                       d_'8804''45'refl_2900
                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (0 :: Integer) v1)
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_'8804''45'trans_2908
                          (coe d_m'8760'n'8804'm_5184 (coe v3) (coe v2))
                          (coe d_n'8804'1'43'n_2988 (coe v3))))
-- Data.Nat.Properties.m≮m∸n
d_m'8814'm'8760'n_5198 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'8814'm'8760'n_5198 = erased
-- Data.Nat.Properties.1+m≢m∸n
d_1'43'm'8802'm'8760'n_5210 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43'm'8802'm'8760'n_5210 = erased
-- Data.Nat.Properties.∸-mono
d_'8760''45'mono_5218 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono_5218 v0 v1 v2 v3 v4 v5
  = let v6
          = seq
              (coe v5)
              (coe
                 du_'8804''45'trans_2908
                 (coe d_m'8760'n'8804'm_5184 (coe v0) (coe v2)) (coe v4)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
           -> case coe v5 of
                MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                  -> coe
                       du_'8804''45'trans_2908
                       (coe d_m'8760'n'8804'm_5184 (coe v0) (coe v2))
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v10
                  -> case coe v2 of
                       _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                           case coe v3 of
                             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                                 coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                             _ -> coe v6
                       _ -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
           -> let v10
                    = seq
                        (coe v5)
                        (coe
                           du_'8804''45'trans_2908
                           (coe d_m'8760'n'8804'm_5184 (coe v0) (coe v2))
                           (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)) in
              coe
                (case coe v0 of
                   _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
                       let v11 = subInt (coe v0) (coe (1 :: Integer)) in
                       coe
                         (let v12
                                = seq
                                    (coe v5)
                                    (coe
                                       du_'8804''45'trans_2908
                                       (coe d_m'8760'n'8804'm_5184 (coe v0) (coe v2))
                                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)) in
                          coe
                            (case coe v1 of
                               _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                                   let v13 = subInt (coe v1) (coe (1 :: Integer)) in
                                   coe
                                     (case coe v5 of
                                        MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                          -> coe
                                               du_'8804''45'trans_2908
                                               (coe d_m'8760'n'8804'm_5184 (coe v0) (coe v2))
                                               (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)
                                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v16
                                          -> case coe v2 of
                                               _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                                                   let v17 = subInt (coe v2) (coe (1 :: Integer)) in
                                                   coe
                                                     (case coe v3 of
                                                        _ | coe
                                                              geqInt (coe v3)
                                                              (coe (1 :: Integer)) ->
                                                            let v18
                                                                  = subInt
                                                                      (coe v3)
                                                                      (coe (1 :: Integer)) in
                                                            coe
                                                              (coe
                                                                 d_'8760''45'mono_5218 (coe v11)
                                                                 (coe v13) (coe v17) (coe v18)
                                                                 (coe v9) (coe v16))
                                                        _ -> coe v12)
                                               _ -> coe v12
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> coe v12))
                   _ -> coe v10)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.∸-monoˡ-≤
d_'8760''45'mono'737''45''8804'_5232 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono'737''45''8804'_5232 v0 v1 v2 v3
  = coe
      d_'8760''45'mono_5218 (coe v0) (coe v1) (coe v2) (coe v2) (coe v3)
      (coe d_'8804''45'refl_2900 (coe v2))
-- Data.Nat.Properties.∸-monoʳ-≤
d_'8760''45'mono'691''45''8804'_5240 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono'691''45''8804'_5240 v0 v1 v2 v3
  = coe
      d_'8760''45'mono_5218 (coe v2) (coe v2) (coe v1) (coe v0)
      (coe d_'8804''45'refl_2900 (coe v2)) (coe v3)
-- Data.Nat.Properties.∸-monoˡ-<
d_'8760''45'mono'737''45''60'_5250 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono'737''45''60'_5250 ~v0 v1 ~v2 v3 v4
  = du_'8760''45'mono'737''45''60'_5250 v1 v3 v4
du_'8760''45'mono'737''45''60'_5250 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8760''45'mono'737''45''60'_5250 v0 v1 v2
  = case coe v0 of
      0 -> coe v1
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
                  -> case coe v2 of
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                         -> coe
                              du_'8760''45'mono'737''45''60'_5250 (coe v3) (coe v6) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.∸-monoʳ-<
d_'8760''45'mono'691''45''60'_5276 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono'691''45''60'_5276 v0 v1 v2 v3 v4
  = let v5 = subInt (coe v1) (coe (1 :: Integer)) in
    coe
      (case coe v2 of
         0 -> coe
                seq (coe v3)
                (coe
                   seq (coe v4)
                   (coe
                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                      (d_m'8760'n'8804'm_5184
                         (coe subInt (coe v0) (coe (1 :: Integer))) (coe v5))))
         _ -> let v6 = subInt (coe v2) (coe (1 :: Integer)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                     -> case coe v4 of
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12
                            -> let v13 = subInt (coe v0) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    d_'8760''45'mono'691''45''60'_5276 (coe v13) (coe v5) (coe v6)
                                    (coe v9) (coe v12))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Nat.Properties.∸-cancelʳ-≤
d_'8760''45'cancel'691''45''8804'_5298 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'cancel'691''45''8804'_5298 ~v0 v1 ~v2 v3 ~v4
  = du_'8760''45'cancel'691''45''8804'_5298 v1 v3
du_'8760''45'cancel'691''45''8804'_5298 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8760''45'cancel'691''45''8804'_5298 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> case coe v0 of
             0 -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             _ -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe du_'8760''45'cancel'691''45''8804'_5298 (coe v5) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.∸-cancelʳ-<
d_'8760''45'cancel'691''45''60'_5318 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'cancel'691''45''60'_5318 v0 v1 ~v2 ~v3
  = du_'8760''45'cancel'691''45''60'_5318 v0 v1
du_'8760''45'cancel'691''45''60'_5318 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8760''45'cancel'691''45''60'_5318 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe du_0'60'1'43'n_3216
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe du_'8760''45'cancel'691''45''60'_5318 (coe v2) (coe v3))))
-- Data.Nat.Properties.∸-cancelˡ-≡
d_'8760''45'cancel'737''45''8801'_5338 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'cancel'737''45''8801'_5338 = erased
-- Data.Nat.Properties.∸-cancelʳ-≡
d_'8760''45'cancel'691''45''8801'_5354 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'cancel'691''45''8801'_5354 = erased
-- Data.Nat.Properties.m∸n≡0⇒m≤n
d_m'8760'n'8801'0'8658'm'8804'n_5364 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'8801'0'8658'm'8804'n_5364 v0 ~v1 ~v2
  = du_m'8760'n'8801'0'8658'm'8804'n_5364 v0
du_m'8760'n'8801'0'8658'm'8804'n_5364 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8760'n'8801'0'8658'm'8804'n_5364 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_m'8760'n'8801'0'8658'm'8804'n_5364 (coe v1)))
-- Data.Nat.Properties.m≤n⇒m∸n≡0
d_m'8804'n'8658'm'8760'n'8801'0_5372 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8760'n'8801'0_5372 = erased
-- Data.Nat.Properties.m<n⇒0<n∸m
d_m'60'n'8658'0'60'n'8760'm_5378 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'0'60'n'8760'm_5378 v0 ~v1 v2
  = du_m'60'n'8658'0'60'n'8760'm_5378 v0 v2
du_m'60'n'8658'0'60'n'8760'm_5378 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'0'60'n'8760'm_5378 v0 v1
  = case coe v0 of
      0 -> coe du_0'60'1'43'n_3216
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe du_m'60'n'8658'0'60'n'8760'm_5378 (coe v2) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m∸n≢0⇒n<m
d_m'8760'n'8802'0'8658'n'60'm_5388 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'8802'0'8658'n'60'm_5388 v0 v1 ~v2
  = du_m'8760'n'8802'0'8658'n'60'm_5388 v0 v1
du_m'8760'n'8802'0'8658'n'60'm_5388 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8760'n'8802'0'8658'n'60'm_5388 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v2 ->
                 coe
                   du_'8804''7495''8658''8804'_2854
                   (coe addInt (coe (1 :: Integer)) (coe v1)))
              (coe du_'8804''8658''8804''7495'_2866)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                    (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v0))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5 -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                          erased)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m>n⇒m∸n≢0
d_m'62'n'8658'm'8760'n'8802'0_5416 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'62'n'8658'm'8760'n'8802'0_5416 = erased
-- Data.Nat.Properties.m≤n⇒n∸m≤n
d_m'8804'n'8658'n'8760'm'8804'n_5422 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'n'8760'm'8804'n_5422 ~v0 v1 v2
  = du_m'8804'n'8658'n'8760'm'8804'n_5422 v1 v2
du_m'8804'n'8658'n'8760'm'8804'n_5422 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'n'8760'm'8804'n_5422 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             d_'8804''45'refl_2900
             (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (0 :: Integer))
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_m'8804'n'8658'n'8760'm'8804'n_5422 (coe v5) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.+-∸-comm
d_'43''45''8760''45'comm_5432 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45''8760''45'comm_5432 = erased
-- Data.Nat.Properties.∸-+-assoc
d_'8760''45''43''45'assoc_5450 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45''43''45'assoc_5450 = erased
-- Data.Nat.Properties.+-∸-assoc
d_'43''45''8760''45'assoc_5474 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45''8760''45'assoc_5474 = erased
-- Data.Nat.Properties.m≤n+o⇒m∸n≤o
d_m'8804'n'43'o'8658'm'8760'n'8804'o_5496 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'o'8658'm'8760'n'8804'o_5496 v0 v1 ~v2 v3
  = du_m'8804'n'43'o'8658'm'8760'n'8804'o_5496 v0 v1 v3
du_m'8804'n'43'o'8658'm'8760'n'8804'o_5496 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'43'o'8658'm'8760'n'8804'o_5496 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_m'8804'n'43'o'8658'm'8760'n'8804'o_5496 (coe v4) (coe v3)
                          (coe
                             MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v2))))
-- Data.Nat.Properties.m<n+o⇒m∸n<o
d_m'60'n'43'o'8658'm'8760'n'60'o_5516 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'43'o'8658'm'8760'n'60'o_5516 v0 v1 ~v2 ~v3 v4
  = du_m'60'n'43'o'8658'm'8760'n'60'o_5516 v0 v1 v4
du_m'60'n'43'o'8658'm'8760'n'60'o_5516 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'43'o'8658'm'8760'n'60'o_5516 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_m'60'n'43'o'8658'm'8760'n'60'o_5516 (coe v4) (coe v3)
                          (coe MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70 (coe v2))))
-- Data.Nat.Properties.m+n≤o⇒m≤o∸n
d_m'43'n'8804'o'8658'm'8804'o'8760'n_5540 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'43'n'8804'o'8658'm'8804'o'8760'n_5540 v0 ~v1 ~v2 v3
  = du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540 v0 v3
du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe du_m'43'n'8804'o'8658'm'8804'o'8760'n_5540 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m≤o∸n⇒m+n≤o
d_m'8804'o'8760'n'8658'm'43'n'8804'o_5560 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'o'8760'n'8658'm'43'n'8804'o_5560 ~v0 ~v1 ~v2 v3 v4
  = du_m'8804'o'8760'n'8658'm'43'n'8804'o_5560 v3 v4
du_m'8804'o'8760'n'8658'm'43'n'8804'o_5560 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'o'8760'n'8658'm'43'n'8804'o_5560 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26 -> coe v1
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_m'8804'o'8760'n'8658'm'43'n'8804'o_5560 (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.m≤n+m∸n
d_m'8804'n'43'm'8760'n_5586 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'm'8760'n_5586 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe d_'8804''45'refl_2900 (coe v0)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (d_m'8804'n'43'm'8760'n_5586 (coe v2) (coe v3))))
-- Data.Nat.Properties.m+n∸n≡m
d_m'43'n'8760'n'8801'm_5600 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43'n'8760'n'8801'm_5600 = erased
-- Data.Nat.Properties.m+n∸m≡n
d_m'43'n'8760'm'8801'n_5612 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43'n'8760'm'8801'n_5612 = erased
-- Data.Nat.Properties.m+[n∸m]≡n
d_m'43''91'n'8760'm'93''8801'n_5620 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43''91'n'8760'm'93''8801'n_5620 = erased
-- Data.Nat.Properties.m∸n+n≡m
d_m'8760'n'43'n'8801'm_5634 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8760'n'43'n'8801'm_5634 = erased
-- Data.Nat.Properties.m∸[m∸n]≡n
d_m'8760''91'm'8760'n'93''8801'n_5646 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8760''91'm'8760'n'93''8801'n_5646 = erased
-- Data.Nat.Properties.[m+n]∸[m+o]≡n∸o
d_'91'm'43'n'93''8760''91'm'43'o'93''8801'n'8760'o_5662 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'43'n'93''8760''91'm'43'o'93''8801'n'8760'o_5662 = erased
-- Data.Nat.Properties.*-distribʳ-∸
d_'42''45'distrib'691''45''8760'_5674 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8760'_5674 = erased
-- Data.Nat.Properties.*-distribˡ-∸
d_'42''45'distrib'737''45''8760'_5694 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8760'_5694 = erased
-- Data.Nat.Properties.*-distrib-∸
d_'42''45'distrib'45''8760'_5696 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''8760'_5696
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.even≢odd
d_even'8802'odd_5702 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_even'8802'odd_5702 = erased
-- Data.Nat.Properties.m⊓n+n∸m≡n
d_m'8851'n'43'n'8760'm'8801'n_5718 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8851'n'43'n'8760'm'8801'n_5718 = erased
-- Data.Nat.Properties.[m∸n]⊓[n∸m]≡0
d_'91'm'8760'n'93''8851''91'n'8760'm'93''8801'0_5732 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'8760'n'93''8851''91'n'8760'm'93''8801'0_5732 = erased
-- Data.Nat.Properties.∸-distribˡ-⊓-⊔
d_'8760''45'distrib'737''45''8851''45''8852'_5748 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'distrib'737''45''8851''45''8852'_5748 = erased
-- Data.Nat.Properties.∸-distribʳ-⊓
d_'8760''45'distrib'691''45''8851'_5756 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'distrib'691''45''8851'_5756 = erased
-- Data.Nat.Properties.∸-distribˡ-⊔-⊓
d_'8760''45'distrib'737''45''8852''45''8851'_5770 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'distrib'737''45''8852''45''8851'_5770 = erased
-- Data.Nat.Properties.∸-distribʳ-⊔
d_'8760''45'distrib'691''45''8852'_5778 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'distrib'691''45''8852'_5778 = erased
-- Data.Nat.Properties.pred[n]≤n
d_pred'91'n'93''8804'n_5786 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'91'n'93''8804'n_5786 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d_n'8804'1'43'n_2988 (coe v1))
-- Data.Nat.Properties.≤pred⇒≤
d_'8804'pred'8658''8804'_5790 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804'pred'8658''8804'_5790 ~v0 v1 v2
  = du_'8804'pred'8658''8804'_5790 v1 v2
du_'8804'pred'8658''8804'_5790 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804'pred'8658''8804'_5790 v0 v1 = coe seq (coe v0) (coe v1)
-- Data.Nat.Properties.≤⇒pred≤
d_'8804''8658'pred'8804'_5798 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8658'pred'8804'_5798 v0 ~v1 v2
  = du_'8804''8658'pred'8804'_5798 v0 v2
du_'8804''8658'pred'8804'_5798 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8658'pred'8804'_5798 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'8804''45'trans_2908 (coe d_n'8804'1'43'n_2988 (coe v2))
                (coe v1))
-- Data.Nat.Properties.<⇒≤pred
d_'60''8658''8804'pred_5806 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8658''8804'pred_5806 ~v0 ~v1 v2
  = du_'60''8658''8804'pred_5806 v2
du_'60''8658''8804'pred_5806 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''8658''8804'pred_5806 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.suc-pred
d_suc'45'pred_5814 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'pred_5814 = erased
-- Data.Nat.Properties.pred-mono-≤
d_pred'45'mono'45''8804'_5818 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'45'mono'45''8804'_5818 v0 ~v1 v2
  = du_pred'45'mono'45''8804'_5818 v0 v2
du_pred'45'mono'45''8804'_5818 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pred'45'mono'45''8804'_5818 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> coe
             MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v1)
-- Data.Nat.Properties.pred-mono-<
d_pred'45'mono'45''60'_5822 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'45'mono'45''60'_5822 v0 v1 ~v2
  = du_pred'45'mono'45''60'_5822 v0 v1
du_pred'45'mono'45''60'_5822 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pred'45'mono'45''60'_5822 v0 v1
  = case coe v0 of
      0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
      _ -> case coe v1 of
             0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70
-- Data.Nat.Properties.pred-cancel-≤
d_pred'45'cancel'45''8804'_5824 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_pred'45'cancel'45''8804'_5824 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> case coe v1 of
             0 -> coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
             _ -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v2)
-- Data.Nat.Properties.pred-cancel-<
d_pred'45'cancel'45''60'_5828 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'45'cancel'45''60'_5828 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> case coe v1 of
             0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
-- Data.Nat.Properties.pred-injective
d_pred'45'injective_5830 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'45'injective_5830 = erased
-- Data.Nat.Properties.pred-cancel-≡
d_pred'45'cancel'45''8801'_5836 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_pred'45'cancel'45''8801'_5836 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    (\ v2 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
             _ -> coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                         (coe
                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
      _ -> case coe v1 of
             0 -> coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                         (coe
                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             _ -> coe
                    (\ v2 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
-- Data.Nat.Properties.m≡n⇒∣m-n∣≡0
d_m'8801'n'8658''8739'm'45'n'8739''8801'0_5838 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8801'n'8658''8739'm'45'n'8739''8801'0_5838 = erased
-- Data.Nat.Properties.∣m-n∣≡0⇒m≡n
d_'8739'm'45'n'8739''8801'0'8658'm'8801'n_5842 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'45'n'8739''8801'0'8658'm'8801'n_5842 = erased
-- Data.Nat.Properties.m≤n⇒∣n-m∣≡n∸m
d_m'8804'n'8658''8739'n'45'm'8739''8801'n'8760'm_5852 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658''8739'n'45'm'8739''8801'n'8760'm_5852 = erased
-- Data.Nat.Properties.m≤n⇒∣m-n∣≡n∸m
d_m'8804'n'8658''8739'm'45'n'8739''8801'n'8760'm_5858 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658''8739'm'45'n'8739''8801'n'8760'm_5858 = erased
-- Data.Nat.Properties.∣m-n∣≡m∸n⇒n≤m
d_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5864 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5864 v0 v1 ~v2
  = du_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5864 v0 v1
du_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5864 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5864 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe
                             du_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5864 (coe v2)
                             (coe v3))))
-- Data.Nat.Properties.∣n-n∣≡0
d_'8739'n'45'n'8739''8801'0_5880 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'n'45'n'8739''8801'0_5880 = erased
-- Data.Nat.Properties.∣m-m+n∣≡n
d_'8739'm'45'm'43'n'8739''8801'n_5888 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'45'm'43'n'8739''8801'n_5888 = erased
-- Data.Nat.Properties.∣m+n-m+o∣≡∣n-o∣
d_'8739'm'43'n'45'm'43'o'8739''8801''8739'n'45'o'8739'_5902 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'43'n'45'm'43'o'8739''8801''8739'n'45'o'8739'_5902
  = erased
-- Data.Nat.Properties.m∸n≤∣m-n∣
d_m'8760'n'8804''8739'm'45'n'8739'_5918 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'8804''8739'm'45'n'8739'_5918 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v2 -> coe du_'8804''7495''8658''8804'_2854 (coe v0))
              (coe du_'8804''8658''8804''7495'_2866)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
                       (coe v1)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                else coe
                       d_'8804''45'refl_2900
                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.∣m-n∣≤m⊔n
d_'8739'm'45'n'8739''8804'm'8852'n_5948 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'45'n'8739''8804'm'8852'n_5948 v0 v1
  = case coe v0 of
      0 -> coe
             d_'8804''45'refl_2900
             (coe
                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                (coe (0 :: Integer)) (coe v1))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       d_'8804''45'refl_2900
                       (coe
                          MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v0)
                          (coe (0 :: Integer)))
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe d_'8739'm'45'n'8739''8804'm'8852'n_5948 (coe v2) (coe v3)))
-- Data.Nat.Properties.∣-∣-identityˡ
d_'8739''45''8739''45'identity'737'_5958 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''45'identity'737'_5958 = erased
-- Data.Nat.Properties.∣-∣-identityʳ
d_'8739''45''8739''45'identity'691'_5962 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''45'identity'691'_5962 = erased
-- Data.Nat.Properties.∣-∣-identity
d_'8739''45''8739''45'identity_5966 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8739''45''8739''45'identity_5966
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.∣-∣-comm
d_'8739''45''8739''45'comm_5968 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''45'comm_5968 = erased
-- Data.Nat.Properties.∣m-n∣≡[m∸n]∨[n∸m]
d_'8739'm'45'n'8739''8801''91'm'8760'n'93''8744''91'n'8760'm'93'_5982 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8739'm'45'n'8739''8801''91'm'8760'n'93''8744''91'n'8760'm'93'_5982 v0
                                                                      v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v2 -> coe du_'8804''7495''8658''8804'_2854 (coe v0))
              (coe du_'8804''8658''8804''7495'_2866)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
                       (coe v1)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238)
                          (coe
                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v0)
                             (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                             (\ v5 v6 v7 v8 v9 -> v9)
                             (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                (coe v0) (coe v1))
                             (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                (coe v1) (coe v0))
                             (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                (\ v5 v6 v7 v8 v9 -> v9)
                                (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                   (coe v1) (coe v0))
                                (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
                                (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                      (coe d_'8804''45'isPreorder_2950))
                                   (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0))
                                erased)
                             erased))
                else coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.*-distribˡ-∣-∣
d_'42''45'distrib'737''45''8739''45''8739'_6004 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8739''45''8739'_6004 = erased
-- Data.Nat.Properties.*-distribʳ-∣-∣
d_'42''45'distrib'691''45''8739''45''8739'_6016 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8739''45''8739'_6016 = erased
-- Data.Nat.Properties.*-distrib-∣-∣
d_'42''45'distrib'45''8739''45''8739'_6018 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''8739''45''8739'_6018
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.m≤n+∣n-m∣
d_m'8804'n'43''8739'n'45'm'8739'_6024 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43''8739'n'45'm'8739'_6024 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe d_'8804''45'refl_2900 (coe v0)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (d_m'8804'n'43''8739'n'45'm'8739'_6024 (coe v2) (coe v3))))
-- Data.Nat.Properties.m≤n+∣m-n∣
d_m'8804'n'43''8739'm'45'n'8739'_6038 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43''8739'm'45'n'8739'_6038 v0 v1
  = coe d_m'8804'n'43''8739'n'45'm'8739'_6024 (coe v0) (coe v1)
-- Data.Nat.Properties.m≤∣m-n∣+n
d_m'8804''8739'm'45'n'8739''43'n_6052 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804''8739'm'45'n'8739''43'n_6052 v0 v1
  = coe d_m'8804'n'43''8739'm'45'n'8739'_6038 (coe v0) (coe v1)
-- Data.Nat.Properties.∣-∣-triangle
d_'8739''45''8739''45'triangle_6060 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739''45''8739''45'triangle_6060 v0 v1 v2
  = case coe v0 of
      0 -> coe d_m'8804'n'43''8739'n'45'm'8739'_6024 (coe v2) (coe v1)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                          (coe d_'8804''45'isPreorder_2950)
                          (\ v4 v5 v6 -> coe du_'60''8658''8804'_2998 v6))
                       (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                          (coe v0) (coe v2))
                       (addInt
                          (coe
                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                             (coe (0 :: Integer)) (coe v2))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v0)
                             (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                             (coe d_'8804''45'isPreorder_2950)
                             (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_3128 v7 v8))
                          (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                             (coe v0) (coe v2))
                          (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v2))
                          (addInt
                             (coe
                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                (coe (0 :: Integer)) (coe v2))
                             (coe
                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v0)
                                (coe (0 :: Integer))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                (coe d_'8804''45'isPreorder_2950)
                                (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_3128 v7 v8))
                             (MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v2))
                             (addInt (coe v0) (coe v2))
                             (addInt
                                (coe
                                   MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                   (coe (0 :: Integer)) (coe v2))
                                (coe
                                   MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v0)
                                   (coe (0 :: Integer))))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                (\ v4 v5 v6 v7 v8 -> v8) (addInt (coe v0) (coe v2))
                                (addInt
                                   (coe
                                      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v0)
                                      (coe (0 :: Integer)))
                                   (coe v2))
                                (addInt
                                   (coe
                                      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                      (coe (0 :: Integer)) (coe v2))
                                   (coe
                                      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v0)
                                      (coe (0 :: Integer))))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                      (coe d_'8804''45'isPreorder_2950))
                                   (coe
                                      addInt
                                      (coe
                                         MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                         (coe v0) (coe (0 :: Integer)))
                                      (coe v2)))
                                erased)
                             (d_m'8852'n'8804'm'43'n_4972 (coe v0) (coe v2)))
                          (d_'8739'm'45'n'8739''8804'm'8852'n_5948 (coe v0) (coe v2)))
                _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (case coe v2 of
                          0 -> coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                    (coe d_'8804''45'isPreorder_2950)
                                    (\ v5 v6 v7 -> coe du_'60''8658''8804'_2998 v7))
                                 (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                    (coe v0) (coe (0 :: Integer)))
                                 (addInt
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v0)
                                       (coe v1))
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284 (coe v1)
                                       (coe (0 :: Integer))))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                    (\ v5 v6 v7 v8 v9 -> v9)
                                    (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                       (coe v0) (coe (0 :: Integer)))
                                    v0
                                    (addInt
                                       (coe
                                          MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                          (coe v0) (coe v1))
                                       (coe
                                          MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                          (coe v1) (coe (0 :: Integer))))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                          (coe d_'8804''45'isPreorder_2950)
                                          (\ v5 v6 v7 v8 v9 ->
                                             coe du_'8804''45''60''45'trans_3128 v8 v9))
                                       v0
                                       (addInt
                                          (coe
                                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                             (coe v0) (coe v1))
                                          (coe v1))
                                       (addInt
                                          (coe
                                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                             (coe v0) (coe v1))
                                          (coe
                                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                             (coe v1) (coe (0 :: Integer))))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                          (\ v5 v6 v7 v8 v9 -> v9)
                                          (addInt
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                                (coe v0) (coe v1))
                                             (coe v1))
                                          (addInt
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                                (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                                (coe v1) (coe (0 :: Integer))))
                                          (addInt
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                                (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                                (coe v1) (coe (0 :: Integer))))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe d_'8804''45'isPreorder_2950))
                                             (coe
                                                addInt
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                                   (coe v0) (coe v1))
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
                                                   (coe v1) (coe (0 :: Integer)))))
                                          erased)
                                       (d_m'8804''8739'm'45'n'8739''43'n_6052 (coe v0) (coe v1)))
                                    erased)
                          _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    d_'8739''45''8739''45'triangle_6060 (coe v3) (coe v4)
                                    (coe v5))))
-- Data.Nat.Properties.∣-∣≡∣-∣′
d_'8739''45''8739''8801''8739''45''8739''8242'_6092 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''8801''8739''45''8739''8242'_6092 = erased
-- Data.Nat.Properties.∣-∣-isProtoMetric
d_'8739''45''8739''45'isProtoMetric_6114 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_'8739''45''8739''45'isProtoMetric_6114
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_constructor_100
      (coe d_'8804''45'isPartialOrder_2954)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
      (coe (\ v0 v1 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Data.Nat.Properties.∣-∣-isPreMetric
d_'8739''45''8739''45'isPreMetric_6116 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_104
d_'8739''45''8739''45'isPreMetric_6116
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_constructor_174
      (coe d_'8739''45''8739''45'isProtoMetric_6114) erased
-- Data.Nat.Properties.∣-∣-isQuasiSemiMetric
d_'8739''45''8739''45'isQuasiSemiMetric_6118 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_178
d_'8739''45''8739''45'isQuasiSemiMetric_6118
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_constructor_252
      (coe d_'8739''45''8739''45'isPreMetric_6116) erased
-- Data.Nat.Properties.∣-∣-isSemiMetric
d_'8739''45''8739''45'isSemiMetric_6120 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_256
d_'8739''45''8739''45'isSemiMetric_6120
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_constructor_334
      (coe d_'8739''45''8739''45'isQuasiSemiMetric_6118) erased
-- Data.Nat.Properties.∣-∣-isMetric
d_'8739''45''8739''45'isMetric_6122 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_340
d_'8739''45''8739''45'isMetric_6122
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_constructor_424
      (coe d_'8739''45''8739''45'isSemiMetric_6120)
      (coe d_'8739''45''8739''45'triangle_6060)
-- Data.Nat.Properties.∣-∣-quasiSemiMetric
d_'8739''45''8739''45'quasiSemiMetric_6124 ::
  MAlonzo.Code.Function.Metric.Nat.Bundles.T_QuasiSemiMetric_190
d_'8739''45''8739''45'quasiSemiMetric_6124
  = coe
      MAlonzo.Code.Function.Metric.Nat.Bundles.C_constructor_284
      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
      d_'8739''45''8739''45'isQuasiSemiMetric_6118
-- Data.Nat.Properties.∣-∣-semiMetric
d_'8739''45''8739''45'semiMetric_6126 ::
  MAlonzo.Code.Function.Metric.Nat.Bundles.T_SemiMetric_290
d_'8739''45''8739''45'semiMetric_6126
  = coe
      MAlonzo.Code.Function.Metric.Nat.Bundles.C_constructor_390
      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
      d_'8739''45''8739''45'isSemiMetric_6120
-- Data.Nat.Properties.∣-∣-preMetric
d_'8739''45''8739''45'preMetric_6128 ::
  MAlonzo.Code.Function.Metric.Nat.Bundles.T_PreMetric_98
d_'8739''45''8739''45'preMetric_6128
  = coe
      MAlonzo.Code.Function.Metric.Nat.Bundles.C_constructor_184
      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
      d_'8739''45''8739''45'isPreMetric_6116
-- Data.Nat.Properties.∣-∣-metric
d_'8739''45''8739''45'metric_6130 ::
  MAlonzo.Code.Function.Metric.Nat.Bundles.T_Metric_396
d_'8739''45''8739''45'metric_6130
  = coe
      MAlonzo.Code.Function.Metric.Nat.Bundles.C_constructor_502
      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_284
      d_'8739''45''8739''45'isMetric_6122
-- Data.Nat.Properties.⌊n/2⌋-mono
d_'8970'n'47'2'8971''45'mono_6132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8970'n'47'2'8971''45'mono_6132 ~v0 ~v1 v2
  = du_'8970'n'47'2'8971''45'mono_6132 v2
du_'8970'n'47'2'8971''45'mono_6132 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8970'n'47'2'8971''45'mono_6132 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_'8970'n'47'2'8971''45'mono_6132 (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.⌈n/2⌉-mono
d_'8968'n'47'2'8969''45'mono_6136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8968'n'47'2'8969''45'mono_6136 ~v0 ~v1 v2
  = du_'8968'n'47'2'8969''45'mono_6136 v2
du_'8968'n'47'2'8969''45'mono_6136 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8968'n'47'2'8969''45'mono_6136 v0
  = coe
      du_'8970'n'47'2'8971''45'mono_6132
      (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v0)
-- Data.Nat.Properties.⌊n/2⌋≤⌈n/2⌉
d_'8970'n'47'2'8971''8804''8968'n'47'2'8969'_6142 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8970'n'47'2'8971''8804''8968'n'47'2'8969'_6142 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      1 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (d_'8970'n'47'2'8971''8804''8968'n'47'2'8969'_6142 (coe v1)))
-- Data.Nat.Properties.⌊n/2⌋+⌈n/2⌉≡n
d_'8970'n'47'2'8971''43''8968'n'47'2'8969''8801'n_6148 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8970'n'47'2'8971''43''8968'n'47'2'8969''8801'n_6148 = erased
-- Data.Nat.Properties.⌊n/2⌋≤n
d_'8970'n'47'2'8971''8804'n_6154 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8970'n'47'2'8971''8804'n_6154 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      1 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (d_'8970'n'47'2'8971''8804'n_6154 (coe v1)))
-- Data.Nat.Properties.⌊n/2⌋<n
d_'8970'n'47'2'8971''60'n_6160 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8970'n'47'2'8971''60'n_6160 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (d_'8970'n'47'2'8971''8804'n_6154 (coe v1))))
-- Data.Nat.Properties.n≡⌊n+n/2⌋
d_n'8801''8970'n'43'n'47'2'8971'_6166 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8801''8970'n'43'n'47'2'8971'_6166 = erased
-- Data.Nat.Properties.⌈n/2⌉≤n
d_'8968'n'47'2'8969''8804'n_6174 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8968'n'47'2'8969''8804'n_6174 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (d_'8970'n'47'2'8971''8804'n_6154 (coe v1)))
-- Data.Nat.Properties.⌈n/2⌉<n
d_'8968'n'47'2'8969''60'n_6180 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8968'n'47'2'8969''60'n_6180 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (d_'8970'n'47'2'8971''60'n_6160 (coe v0))
-- Data.Nat.Properties.n≡⌈n+n/2⌉
d_n'8801''8968'n'43'n'47'2'8969'_6186 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8801''8968'n'43'n'47'2'8969'_6186 = erased
-- Data.Nat.Properties.1≤n!
d_1'8804'n'33'_6194 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'8804'n'33'_6194 v0
  = case coe v0 of
      0 -> coe d_'8804''45'refl_2900 (coe (1 :: Integer))
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'42''45'mono'45''8804'_4214 (coe v0)
                (coe MAlonzo.Code.Data.Nat.Base.d__'33'_336 (coe v1))
                (coe du_m'8804'm'43'n_3624 (coe (1 :: Integer)))
                (coe d_1'8804'n'33'_6194 (coe v1)))
-- Data.Nat.Properties._!≢0
d__'33''8802'0_6200 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d__'33''8802'0_6200 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'62''45'nonZero_138
      (coe d_1'8804'n'33'_6194 (coe v0))
-- Data.Nat.Properties._!*_!≢0
d__'33''42'_'33''8802'0_6208 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d__'33''42'_'33''8802'0_6208 ~v0 ~v1
  = du__'33''42'_'33''8802'0_6208
du__'33''42'_'33''8802'0_6208 ::
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du__'33''42'_'33''8802'0_6208 = coe du_m'42'n'8802'0_3958
-- Data.Nat.Properties.≤′-trans
d_'8804''8242''45'trans_6214 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_'8804''8242''45'trans_6214 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''8242''45'trans_6214 v3 v4
du_'8804''8242''45'trans_6214 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
du_'8804''8242''45'trans_6214 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
        -> coe v0
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352 v3
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352
             (coe du_'8804''8242''45'trans_6214 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.z≤′n
d_z'8804''8242'n_6222 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_z'8804''8242'n_6222 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352
                (d_z'8804''8242'n_6222 (coe v1)))
-- Data.Nat.Properties.s≤′s
d_s'8804''8242's_6226 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_s'8804''8242's_6226 ~v0 ~v1 v2 = du_s'8804''8242's_6226 v2
du_s'8804''8242's_6226 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
du_s'8804''8242's_6226 v0 = coe v0
-- Data.Nat.Properties.≤′⇒≤
d_'8804''8242''8658''8804'_6232 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8242''8658''8804'_6232 v0 ~v1 v2
  = du_'8804''8242''8658''8804'_6232 v0 v2
du_'8804''8242''8658''8804'_6232 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8242''8658''8804'_6232 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
        -> coe du_'8804''45'reflexive_2896 (coe v0)
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352 v3
        -> coe du_'8804''8242''8658''8804'_6232 (coe v0) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤⇒≤′
d_'8804''8658''8804''8242'_6238 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_'8804''8658''8804''8242'_6238 ~v0 v1 v2
  = du_'8804''8658''8804''8242'_6238 v1 v2
du_'8804''8658''8804''8242'_6238 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
du_'8804''8658''8804''8242'_6238 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe d_z'8804''8242'n_6222 (coe v0)
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_'8804''8658''8804''8242'_6238 (coe v5) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤′-step-injective
d_'8804''8242''45'step'45'injective_6246 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8242''45'step'45'injective_6246 = erased
-- Data.Nat.Properties.z<′s
d_z'60''8242's_6248 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_z'60''8242's_6248 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352
                (d_z'60''8242's_6248 (coe v1)))
-- Data.Nat.Properties.s<′s
d_s'60''8242's_6252 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_s'60''8242's_6252 ~v0 ~v1 v2 = du_s'60''8242's_6252 v2
du_s'60''8242's_6252 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
du_s'60''8242's_6252 v0 = coe v0
-- Data.Nat.Properties.<⇒<′
d_'60''8658''60''8242'_6256 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_'60''8658''60''8242'_6256 ~v0 v1 v2
  = du_'60''8658''60''8242'_6256 v1 v2
du_'60''8658''60''8242'_6256 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
du_'60''8658''60''8242'_6256 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                  -> coe d_z'60''8242's_6248 (coe v5)
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                  -> coe
                       du_'60''8658''60''8242'_6256
                       (coe subInt (coe v0) (coe (1 :: Integer)))
                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<′⇒<
d_'60''8242''8658''60'_6260 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8242''8658''60'_6260 v0 ~v1 v2
  = du_'60''8242''8658''60'_6260 v0 v2
du_'60''8242''8658''60'_6260 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''8242''8658''60'_6260 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
        -> coe d_n'60'1'43'n_3220 (coe v0)
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352 v3
        -> coe
             du_m'60'n'8658'm'60'1'43'n_3204
             (coe du_'60''8242''8658''60'_6260 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.m<1+n⇒m<n∨m≡n′
d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n'8242'_6264 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n'8242'_6264 v0 v1 v2
  = let v3
          = coe
              du_'60''8658''60''8242'_6256
              (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
         MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352 v5
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe du_'60''8242''8658''60'_6260 (coe v0) (coe v5))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties._≤′?_
d__'8804''8242''63'__6278 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''8242''63'__6278 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (coe du_'8804''8658''8804''8242'_6238 (coe v1))
      (coe du_'8804''8242''8658''8804'_6232 (coe v0))
      (coe d__'8804''63'__2920 (coe v0) (coe v1))
-- Data.Nat.Properties._<′?_
d__'60''8242''63'__6284 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''8242''63'__6284 v0 v1
  = coe
      d__'8804''8242''63'__6278
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Nat.Properties._≥′?_
d__'8805''8242''63'__6290 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''8242''63'__6290 v0 v1
  = coe d__'8804''8242''63'__6278 (coe v1) (coe v0)
-- Data.Nat.Properties._>′?_
d__'62''8242''63'__6292 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''8242''63'__6292 v0 v1
  = coe d__'60''8242''63'__6284 (coe v1) (coe v0)
-- Data.Nat.Properties.m≤′m+n
d_m'8804''8242'm'43'n_6298 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_m'8804''8242'm'43'n_6298 v0 v1
  = coe
      du_'8804''8658''8804''8242'_6238 (coe addInt (coe v0) (coe v1))
      (coe du_m'8804'm'43'n_3624 (coe v0))
-- Data.Nat.Properties.n≤′m+n
d_n'8804''8242'm'43'n_6308 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_n'8804''8242'm'43'n_6308 v0 ~v1 = du_n'8804''8242'm'43'n_6308 v0
du_n'8804''8242'm'43'n_6308 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
du_n'8804''8242'm'43'n_6308 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352
                (coe du_n'8804''8242'm'43'n_6308 (coe v1)))
-- Data.Nat.Properties.⌈n/2⌉≤′n
d_'8968'n'47'2'8969''8804''8242'n_6318 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_'8968'n'47'2'8969''8804''8242'n_6318 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
      1 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352
                (d_'8968'n'47'2'8969''8804''8242'n_6318 (coe v1)))
-- Data.Nat.Properties.⌊n/2⌋≤′n
d_'8970'n'47'2'8971''8804''8242'n_6324 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_'8970'n'47'2'8971''8804''8242'n_6324 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352
                (d_'8968'n'47'2'8969''8804''8242'n_6318 (coe v1)))
-- Data.Nat.Properties.≤⇒≤″
d_'8804''8658''8804''8243'_6328 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
d_'8804''8658''8804''8243'_6328 v0 v1 ~v2
  = du_'8804''8658''8804''8243'_6328 v0 v1
du_'8804''8658''8804''8243'_6328 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
du_'8804''8658''8804''8243'_6328 v0 v1
  = coe
      MAlonzo.Code.Algebra.Definitions.RawMagma.C__'44'__42
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0) erased
-- Data.Nat.Properties.<⇒<″
d_'60''8658''60''8243'_6332 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
d_'60''8658''60''8243'_6332 v0 v1 v2
  = coe
      du_'8804''8658''8804''8243'_6328
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Nat.Properties.≤″⇒≤
d_'8804''8243''8658''8804'_6334 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8243''8658''8804'_6334 v0 ~v1 v2
  = du_'8804''8243''8658''8804'_6334 v0 v2
du_'8804''8243''8658''8804'_6334 ::
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8243''8658''8804'_6334 v0 v1
  = coe seq (coe v1) (coe du_m'8804'm'43'n_3624 (coe v0))
-- Data.Nat.Properties.≤″-proof
d_'8804''8243''45'proof_6342 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8243''45'proof_6342 = erased
-- Data.Nat.Properties.m≤n⇒∃[o]m+o≡n
d_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6348 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6348 v0 v1 ~v2
  = du_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6348 v0 v1
du_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6348 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6348 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0) erased
-- Data.Nat.Properties.guarded-∸≗∸
d_guarded'45''8760''8791''8760'_6360 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guarded'45''8760''8791''8760'_6360 = erased
-- Data.Nat.Properties.m<ᵇn⇒1+m+[n-1+m]≡n
d_m'60''7495'n'8658'1'43'm'43''91'n'45'1'43'm'93''8801'n_6368 ::
  Integer ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'60''7495'n'8658'1'43'm'43''91'n'45'1'43'm'93''8801'n_6368
  = erased
-- Data.Nat.Properties.m<ᵇ1+m+n
d_m'60''7495'1'43'm'43'n_6380 :: Integer -> Integer -> AgdaAny
d_m'60''7495'1'43'm'43'n_6380 v0 ~v1
  = du_m'60''7495'1'43'm'43'n_6380 v0
du_m'60''7495'1'43'm'43'n_6380 :: Integer -> AgdaAny
du_m'60''7495'1'43'm'43'n_6380 v0
  = coe
      du_'60''8658''60''7495'_2836
      (coe
         du_m'8804'm'43'n_3624 (coe addInt (coe (1 :: Integer)) (coe v0)))
-- Data.Nat.Properties.<ᵇ⇒<″
d_'60''7495''8658''60''8243'_6384 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
d_'60''7495''8658''60''8243'_6384 v0 v1 ~v2
  = du_'60''7495''8658''60''8243'_6384 v0 v1
du_'60''7495''8658''60''8243'_6384 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
du_'60''7495''8658''60''8243'_6384 v0 v1
  = coe
      d_'60''8658''60''8243'_6332 v0 v1
      (coe du_'60''7495''8658''60'_2824 (coe v0))
-- Data.Nat.Properties.<″⇒<ᵇ
d_'60''8243''8658''60''7495'_6394 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  AgdaAny
d_'60''8243''8658''60''7495'_6394 v0 ~v1 v2
  = du_'60''8243''8658''60''7495'_6394 v0 v2
du_'60''8243''8658''60''7495'_6394 ::
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  AgdaAny
du_'60''8243''8658''60''7495'_6394 v0 v1
  = coe
      seq (coe v1)
      (coe
         du_'60''8658''60''7495'_2836
         (coe
            du_m'8804'm'43'n_3624 (coe addInt (coe (1 :: Integer)) (coe v0))))
-- Data.Nat.Properties._<″?_
d__'60''8243''63'__6400 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''8243''63'__6400 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (\ v2 -> coe du_'60''7495''8658''60''8243'_6384 (coe v0) (coe v1))
      (coe du_'60''8243''8658''60''7495'_6394 (coe v0))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
         (coe ltInt (coe v0) (coe v1)))
-- Data.Nat.Properties._≤″?_
d__'8804''8243''63'__6406 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''8243''63'__6406 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMagma.C__'44'__42 (coe v1)
                   erased))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d__'60''8243''63'__6400 (coe v2) (coe v1))
-- Data.Nat.Properties._≥″?_
d__'8805''8243''63'__6414 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''8243''63'__6414 v0 v1
  = coe d__'8804''8243''63'__6406 (coe v1) (coe v0)
-- Data.Nat.Properties._>″?_
d__'62''8243''63'__6416 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''8243''63'__6416 v0 v1
  = coe d__'60''8243''63'__6400 (coe v1) (coe v0)
-- Data.Nat.Properties.≤″-irrelevant
d_'8804''8243''45'irrelevant_6418 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8243''45'irrelevant_6418 = erased
-- Data.Nat.Properties.<″-irrelevant
d_'60''8243''45'irrelevant_6432 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8243''45'irrelevant_6432 = erased
-- Data.Nat.Properties.>″-irrelevant
d_'62''8243''45'irrelevant_6434 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''8243''45'irrelevant_6434 = erased
-- Data.Nat.Properties.≥″-irrelevant
d_'8805''8243''45'irrelevant_6436 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8805''8243''45'irrelevant_6436 = erased
-- Data.Nat.Properties.≤‴⇒≤″
d_'8804''8244''8658''8804''8243'_6438 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
d_'8804''8244''8658''8804''8243'_6438 ~v0 ~v1 v2
  = du_'8804''8244''8658''8804''8243'_6438 v2
du_'8804''8244''8658''8804''8243'_6438 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
du_'8804''8244''8658''8804''8243'_6438 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8244''45'reflexive_434
        -> coe
             MAlonzo.Code.Algebra.Definitions.RawMagma.C__'44'__42
             (coe (0 :: Integer)) erased
      MAlonzo.Code.Data.Nat.Base.C_'8804''8244''45'step_436 v1
        -> coe
             MAlonzo.Code.Algebra.Definitions.RawMagma.C__'44'__42
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMagma.d_quotient_38
                   (coe du_'8804''8244''8658''8804''8243'_6438 (coe v1))))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.m≤‴m+k
d_m'8804''8244'm'43'k_6442 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
d_m'8804''8244'm'43'k_6442 ~v0 v1 ~v2
  = du_m'8804''8244'm'43'k_6442 v1
du_m'8804''8244'm'43'k_6442 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
du_m'8804''8244'm'43'k_6442 v0
  = case coe v0 of
      0 -> coe
             (\ v1 ->
                coe MAlonzo.Code.Data.Nat.Base.C_'8804''8244''45'reflexive_434)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                (\ v2 ->
                   coe
                     MAlonzo.Code.Data.Nat.Base.C_'8804''8244''45'step_436
                     (coe du_m'8804''8244'm'43'k_6442 v1 erased)))
-- Data.Nat.Properties.≤″⇒≤‴
d_'8804''8243''8658''8804''8244'_6444 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
d_'8804''8243''8658''8804''8244'_6444 ~v0 ~v1 v2
  = du_'8804''8243''8658''8804''8244'_6444 v2
du_'8804''8243''8658''8804''8244'_6444 ::
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
du_'8804''8243''8658''8804''8244'_6444 v0
  = coe
      du_m'8804''8244'm'43'k_6442
      (MAlonzo.Code.Algebra.Definitions.RawMagma.d_quotient_38 (coe v0))
      erased
-- Data.Nat.Properties.0≤‴n
d_0'8804''8244'n_6446 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
d_0'8804''8244'n_6446 v0
  = coe du_m'8804''8244'm'43'k_6442 v0 erased
-- Data.Nat.Properties.<ᵇ⇒<‴
d_'60''7495''8658''60''8244'_6448 ::
  Integer ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
d_'60''7495''8658''60''8244'_6448 v0 v1 ~v2
  = du_'60''7495''8658''60''8244'_6448 v0 v1
du_'60''7495''8658''60''8244'_6448 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
du_'60''7495''8658''60''8244'_6448 v0 v1
  = coe
      du_'8804''8243''8658''8804''8244'_6444
      (coe du_'60''7495''8658''60''8243'_6384 (coe v0) (coe v1))
-- Data.Nat.Properties.<‴⇒<ᵇ
d_'60''8244''8658''60''7495'_6450 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 -> AgdaAny
d_'60''8244''8658''60''7495'_6450 v0 ~v1 v2
  = du_'60''8244''8658''60''7495'_6450 v0 v2
du_'60''8244''8658''60''7495'_6450 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 -> AgdaAny
du_'60''8244''8658''60''7495'_6450 v0 v1
  = coe
      du_'60''8243''8658''60''7495'_6394 (coe v0)
      (coe du_'8804''8244''8658''8804''8243'_6438 (coe v1))
-- Data.Nat.Properties._<‴?_
d__'60''8244''63'__6452 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''8244''63'__6452 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (\ v2 -> coe du_'60''7495''8658''60''8244'_6448 (coe v0) (coe v1))
      (coe du_'60''8244''8658''60''7495'_6450 (coe v0))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
         (coe ltInt (coe v0) (coe v1)))
-- Data.Nat.Properties._≤‴?_
d__'8804''8244''63'__6458 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''8244''63'__6458 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe d_0'8804''8244'n_6446 (coe v1)))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d__'60''8244''63'__6452 (coe v2) (coe v1))
-- Data.Nat.Properties._≥‴?_
d__'8805''8244''63'__6466 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''8244''63'__6466 v0 v1
  = coe d__'8804''8244''63'__6458 (coe v1) (coe v0)
-- Data.Nat.Properties._>‴?_
d__'62''8244''63'__6468 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''8244''63'__6468 v0 v1
  = coe d__'60''8244''63'__6452 (coe v1) (coe v0)
-- Data.Nat.Properties.≤⇒≤‴
d_'8804''8658''8804''8244'_6470 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
d_'8804''8658''8804''8244'_6470 v0 v1 ~v2
  = du_'8804''8658''8804''8244'_6470 v0 v1
du_'8804''8658''8804''8244'_6470 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422
du_'8804''8658''8804''8244'_6470 v0 v1
  = coe
      du_'8804''8243''8658''8804''8244'_6444
      (coe du_'8804''8658''8804''8243'_6328 (coe v0) (coe v1))
-- Data.Nat.Properties.≤‴⇒≤
d_'8804''8244''8658''8804'_6472 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8244''8658''8804'_6472 v0 ~v1 v2
  = du_'8804''8244''8658''8804'_6472 v0 v2
du_'8804''8244''8658''8804'_6472 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8244''8658''8804'_6472 v0 v1
  = coe
      du_'8804''8243''8658''8804'_6334 (coe v0)
      (coe du_'8804''8244''8658''8804''8243'_6438 (coe v1))
-- Data.Nat.Properties.<‴-irrefl
d_'60''8244''45'irrefl_6474 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8244''45'irrefl_6474 = erased
-- Data.Nat.Properties.≤‴-irrelevant
d_'8804''8244''45'irrelevant_6478 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8244''45'irrelevant_6478 = erased
-- Data.Nat.Properties.<‴-irrelevant
d_'60''8244''45'irrelevant_6504 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8244''45'irrelevant_6504 = erased
-- Data.Nat.Properties.>‴-irrelevant
d_'62''8244''45'irrelevant_6506 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''8244''45'irrelevant_6506 = erased
-- Data.Nat.Properties.≥‴-irrelevant
d_'8805''8244''45'irrelevant_6508 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__422 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8805''8244''45'irrelevant_6508 = erased
-- Data.Nat.Properties.eq?
d_eq'63'_6514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eq'63'_6514 ~v0 ~v1 v2 = du_eq'63'_6514 v2
du_eq'63'_6514 ::
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_eq'63'_6514 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.du_via'45'injection_180
      (coe v0) (coe d__'8799'__2796)
-- Data.Nat.Properties._.anyUpTo?
d_anyUpTo'63'_6532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_anyUpTo'63'_6532 ~v0 ~v1 v2 v3 = du_anyUpTo'63'_6532 v2 v3
du_anyUpTo'63'_6532 ::
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_anyUpTo'63'_6532 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v3 = coe v0 v2 in
              coe
                (let v4 = coe du_anyUpTo'63'_6532 (coe v0) (coe v2) in
                 coe
                   (let v5
                          = case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                                -> coe
                                     seq (coe v5)
                                     (case coe v6 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                         (coe v6))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError in
                    coe
                      (case coe v3 of
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                           -> let v8
                                    = case coe v4 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                 -> case coe v9 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                               -> coe seq (coe v12) (coe v4)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> coe v5
                                               _ -> coe v5
                                        _ -> MAlonzo.RTE.mazUnreachableError in
                              coe
                                (if coe v6
                                   then let v9
                                              = case coe v4 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                    -> case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                                  -> case coe v11 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                         -> coe
                                                                              seq (coe v13) (coe v4)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> coe v8
                                                         _ -> coe v8
                                                  _ -> MAlonzo.RTE.mazUnreachableError in
                                        coe
                                          (case coe v7 of
                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                               -> coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v2)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe d_'8804''45'refl_2900 (coe v1))
                                                             (coe v10))))
                                             _ -> coe v9)
                                   else (case coe v4 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                             -> if coe v9
                                                  then case coe v10 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                           -> case coe v11 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                  -> coe seq (coe v13) (coe v4)
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> coe v8
                                                  else (case coe v7 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                   -> coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe v9)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                 _ -> coe v8
                                                          _ -> coe v8)
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                         _ -> MAlonzo.RTE.mazUnreachableError))))
-- Data.Nat.Properties._._.¬Pn<1+v
d_'172'Pn'60'1'43'v_6566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'Pn'60'1'43'v_6566 = erased
-- Data.Nat.Properties._.allUpTo?
d_allUpTo'63'_6596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_allUpTo'63'_6596 ~v0 ~v1 v2 v3 = du_allUpTo'63'_6596 v2 v3
du_allUpTo'63'_6596 ::
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_allUpTo'63'_6596 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v3 = coe v0 v2 in
              coe
                (let v4 = coe du_allUpTo'63'_6596 (coe v0) (coe v2) in
                 coe
                   (let v5
                          = case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                                -> coe
                                     seq (coe v5)
                                     (coe
                                        seq (coe v6)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                              _ -> MAlonzo.RTE.mazUnreachableError in
                    coe
                      (case coe v3 of
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                           -> let v8
                                    = case coe v4 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                 -> case coe v9 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v8)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                      _ -> coe v5
                                               _ -> coe v5
                                        _ -> MAlonzo.RTE.mazUnreachableError in
                              coe
                                (if coe v6
                                   then case coe v4 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                            -> if coe v9
                                                 then case coe v7 of
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                          -> case coe v10 of
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                                 -> coe
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                      (coe v9)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                         (coe
                                                                            du_Pn'60'1'43'v_6628
                                                                            (coe v2) (coe v11)
                                                                            (coe v12)))
                                                               _ -> coe v8
                                                        _ -> coe v8
                                                 else (case coe v10 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                           -> coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                (coe v9)
                                                                (coe
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                         _ -> coe v8)
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                   else (let v9
                                               = case coe v4 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                     -> case coe v9 of
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                   -> coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe v9)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                 _ -> coe v8
                                                          _ -> coe v8
                                                   _ -> MAlonzo.RTE.mazUnreachableError in
                                         coe
                                           (case coe v7 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                -> coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v6)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                              _ -> coe v9)))
                         _ -> MAlonzo.RTE.mazUnreachableError))))
-- Data.Nat.Properties._._.Pn<1+v
d_Pn'60'1'43'v_6628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_Pn'60'1'43'v_6628 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_Pn'60'1'43'v_6628 v3 v4 v5 v6 v7
du_Pn'60'1'43'v_6628 ::
  Integer ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
du_Pn'60'1'43'v_6628 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
        -> let v8
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased (\ v8 -> coe du_'8801''8658''8801''7495'_2786 (coe v3))
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                        (coe eqInt (coe v3) (coe v0))) in
           coe
             (case coe v8 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                  -> if coe v9
                       then coe seq (coe v10) (coe v1)
                       else coe
                              seq (coe v10)
                              (coe
                                 v2 v3 (coe du_'8804''8743''8802''8658''60'_3060 (coe v0) (coe v7)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.∀[m≤n⇒m≢o]⇒o<n
d_'8704''91'm'8804'n'8658'm'8802'o'93''8658'o'60'n_6654 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8704''91'm'8804'n'8658'm'8802'o'93''8658'o'60'n_6654 v0 v1 v2
  = coe
      du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3274 v0 v1
-- Data.Nat.Properties.∀[m<n⇒m≢o]⇒o≤n
d_'8704''91'm'60'n'8658'm'8802'o'93''8658'o'8804'n_6662 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8704''91'm'60'n'8658'm'8802'o'93''8658'o'8804'n_6662 v0 v1 v2
  = coe
      du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3302 v0 v1
-- Data.Nat.Properties.*-+-isSemiring
d_'42''45''43''45'isSemiring_6664 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_'42''45''43''45'isSemiring_6664
  = coe d_'43''45''42''45'isSemiring_3872
-- Data.Nat.Properties.*-+-isCommutativeSemiring
d_'42''45''43''45'isCommutativeSemiring_6666 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_'42''45''43''45'isCommutativeSemiring_6666
  = coe d_'43''45''42''45'isCommutativeSemiring_3874
-- Data.Nat.Properties.*-+-semiring
d_'42''45''43''45'semiring_6668 ::
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2356
d_'42''45''43''45'semiring_6668
  = coe d_'43''45''42''45'semiring_3886
-- Data.Nat.Properties.*-+-commutativeSemiring
d_'42''45''43''45'commutativeSemiring_6670 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
d_'42''45''43''45'commutativeSemiring_6670
  = coe d_'43''45''42''45'commutativeSemiring_3888
-- Data.Nat.Properties.∣m+n-m+o∣≡∣n-o|
d_'8739'm'43'n'45'm'43'o'8739''8801''8739'n'45'o'124'_6672 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'43'n'45'm'43'o'8739''8801''8739'n'45'o'124'_6672 = erased
-- Data.Nat.Properties.m≤n⇒n⊔m≡n
d_m'8804'n'8658'n'8852'm'8801'n_6674 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'n'8852'm'8801'n_6674 = erased
-- Data.Nat.Properties.m≤n⇒n⊓m≡m
d_m'8804'n'8658'n'8851'm'8801'm_6676 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'n'8851'm'8801'm_6676 = erased
-- Data.Nat.Properties.n⊔m≡m⇒n≤m
d_n'8852'm'8801'm'8658'n'8804'm_6678 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8852'm'8801'm'8658'n'8804'm_6678
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_4582))
-- Data.Nat.Properties.n⊔m≡n⇒m≤n
d_n'8852'm'8801'n'8658'm'8804'n_6680 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8852'm'8801'n'8658'm'8804'n_6680
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3184
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_4582))
-- Data.Nat.Properties.n≤m⊔n
d_n'8804'm'8852'n_6682 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'm'8852'n_6682
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_4582))
-- Data.Nat.Properties.⊔-least
d_'8852''45'least_6684 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8852''45'least_6684
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_4582))
-- Data.Nat.Properties.⊓-greatest
d_'8851''45'greatest_6686 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'greatest_6686
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580)
-- Data.Nat.Properties.⊔-pres-≤m
d_'8852''45'pres'45''8804'm_6688 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8852''45'pres'45''8804'm_6688
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe d_'8804''45'totalPreorder_2962))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe d_'8852''45'operator_4582))
-- Data.Nat.Properties.⊓-pres-m≤
d_'8851''45'pres'45'm'8804'_6690 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'pres'45'm'8804'_6690
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3394
      (coe d_'8804''45'totalPreorder_2962)
      (coe d_'8851''45'operator_4580)
-- Data.Nat.Properties.⊔-abs-⊓
d_'8852''45'abs'45''8851'_6692 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'abs'45''8851'_6692 = erased
-- Data.Nat.Properties.⊓-abs-⊔
d_'8851''45'abs'45''8852'_6694 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'abs'45''8852'_6694 = erased
-- Data.Nat.Properties.suc[pred[n]]≡n
d_suc'91'pred'91'n'93''93''8801'n_6696 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'91'pred'91'n'93''93''8801'n_6696 = erased
-- Data.Nat.Properties.≤-step
d_'8804''45'step_6702 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'step_6702 ~v0 ~v1 v2 = du_'8804''45'step_6702 v2
du_'8804''45'step_6702 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'step_6702 v0 = coe v0
-- Data.Nat.Properties.≤-stepsˡ
d_'8804''45'steps'737'_6704 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'steps'737'_6704 ~v0 ~v1 ~v2 v3
  = du_'8804''45'steps'737'_6704 v3
du_'8804''45'steps'737'_6704 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'steps'737'_6704 v0 = coe v0
-- Data.Nat.Properties.≤-stepsʳ
d_'8804''45'steps'691'_6706 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'steps'691'_6706 ~v0 ~v1 ~v2 v3
  = du_'8804''45'steps'691'_6706 v3
du_'8804''45'steps'691'_6706 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'steps'691'_6706 v0 = coe v0
-- Data.Nat.Properties.<-step
d_'60''45'step_6708 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'step_6708 v0 v1 v2
  = coe du_m'60'n'8658'm'60'1'43'n_3204 v2
-- Data.Nat.Properties.pred-mono
d_pred'45'mono_6710 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'45'mono_6710 v0 v1 v2
  = coe du_pred'45'mono'45''8804'_5818 v0 v2
-- Data.Nat.Properties.<-transʳ
d_'60''45'trans'691'_6712 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans'691'_6712 v0 v1 v2 v3 v4
  = coe du_'8804''45''60''45'trans_3128 v3 v4
-- Data.Nat.Properties.<-transˡ
d_'60''45'trans'737'_6714 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans'737'_6714 v0 v1 v2 v3 v4
  = coe du_'60''45''8804''45'trans_3134 v3 v4
