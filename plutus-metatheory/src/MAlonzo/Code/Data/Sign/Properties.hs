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

module MAlonzo.Code.Data.Sign.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Sign.Properties._.IsAbelianGroup
d_IsAbelianGroup_8 a0 a1 a2 = ()
-- Data.Sign.Properties._.IsAlternativeMagma
d_IsAlternativeMagma_12 a0 = ()
-- Data.Sign.Properties._.IsBand
d_IsBand_16 a0 = ()
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_20 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsCommutativeBand
d_IsCommutativeBand_24 a0 = ()
-- Data.Sign.Properties._.IsCommutativeMagma
d_IsCommutativeMagma_28 a0 = ()
-- Data.Sign.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_32 a0 a1 = ()
-- Data.Sign.Properties._.IsCommutativeRing
d_IsCommutativeRing_36 a0 a1 a2 a3 a4 = ()
-- Data.Sign.Properties._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_40 a0 = ()
-- Data.Sign.Properties._.IsCommutativeSemiring
d_IsCommutativeSemiring_44 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_48 a0 a1 a2 = ()
-- Data.Sign.Properties._.IsFlexibleMagma
d_IsFlexibleMagma_52 a0 = ()
-- Data.Sign.Properties._.IsGroup
d_IsGroup_56 a0 a1 a2 = ()
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_60 a0 a1 = ()
-- Data.Sign.Properties._.IsIdempotentMagma
d_IsIdempotentMagma_64 a0 = ()
-- Data.Sign.Properties._.IsIdempotentMonoid
d_IsIdempotentMonoid_68 a0 a1 = ()
-- Data.Sign.Properties._.IsIdempotentSemiring
d_IsIdempotentSemiring_72 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsInvertibleMagma
d_IsInvertibleMagma_76 a0 a1 a2 = ()
-- Data.Sign.Properties._.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_80 a0 a1 a2 = ()
-- Data.Sign.Properties._.IsKleeneAlgebra
d_IsKleeneAlgebra_84 a0 a1 a2 a3 a4 = ()
-- Data.Sign.Properties._.IsLeftBolLoop
d_IsLeftBolLoop_88 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsLoop
d_IsLoop_92 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsMagma
d_IsMagma_96 a0 = ()
-- Data.Sign.Properties._.IsMedialMagma
d_IsMedialMagma_100 a0 = ()
-- Data.Sign.Properties._.IsMiddleBolLoop
d_IsMiddleBolLoop_104 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsMonoid
d_IsMonoid_108 a0 a1 = ()
-- Data.Sign.Properties._.IsMoufangLoop
d_IsMoufangLoop_112 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsNearSemiring
d_IsNearSemiring_116 a0 a1 a2 = ()
-- Data.Sign.Properties._.IsNearring
d_IsNearring_120 a0 a1 a2 a3 a4 = ()
-- Data.Sign.Properties._.IsNonAssociativeRing
d_IsNonAssociativeRing_124 a0 a1 a2 a3 a4 = ()
-- Data.Sign.Properties._.IsQuasigroup
d_IsQuasigroup_128 a0 a1 a2 = ()
-- Data.Sign.Properties._.IsQuasiring
d_IsQuasiring_132 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsRightBolLoop
d_IsRightBolLoop_136 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsRing
d_IsRing_140 a0 a1 a2 a3 a4 = ()
-- Data.Sign.Properties._.IsRingWithoutOne
d_IsRingWithoutOne_144 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsSelectiveMagma
d_IsSelectiveMagma_148 a0 = ()
-- Data.Sign.Properties._.IsSemigroup
d_IsSemigroup_152 a0 = ()
-- Data.Sign.Properties._.IsSemimedialMagma
d_IsSemimedialMagma_156 a0 = ()
-- Data.Sign.Properties._.IsSemiring
d_IsSemiring_160 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_164 a0 a1 a2 a3 = ()
-- Data.Sign.Properties._.IsSemiringWithoutOne
d_IsSemiringWithoutOne_168 a0 a1 a2 = ()
-- Data.Sign.Properties._.IsSuccessorSet
d_IsSuccessorSet_172 a0 a1 = ()
-- Data.Sign.Properties._.IsUnitalMagma
d_IsUnitalMagma_176 a0 a1 = ()
-- Data.Sign.Properties._.IsAbelianGroup._//_
d__'47''47'__182 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
d__'47''47'__182 v0 ~v1 v2 ~v3 = du__'47''47'__182 v0 v2
du__'47''47'__182 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
du__'47''47'__182 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Sign.Properties._.IsAbelianGroup.assoc
d_assoc_184 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_184 = erased
-- Data.Sign.Properties._.IsAbelianGroup.comm
d_comm_186 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_186 = erased
-- Data.Sign.Properties._.IsAbelianGroup.identity
d_identity_188 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_188 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))
-- Data.Sign.Properties._.IsAbelianGroup.identityʳ
d_identity'691'_190 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_190 = erased
-- Data.Sign.Properties._.IsAbelianGroup.identityˡ
d_identity'737'_192 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_192 = erased
-- Data.Sign.Properties._.IsAbelianGroup.inverse
d_inverse_194 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_194 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Sign.Properties._.IsAbelianGroup.inverseʳ
d_inverse'691'_196 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_196 = erased
-- Data.Sign.Properties._.IsAbelianGroup.inverseˡ
d_inverse'737'_198 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_198 = erased
-- Data.Sign.Properties._.IsAbelianGroup.isCommutativeMagma
d_isCommutativeMagma_200 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_200 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_200 v3
du_isCommutativeMagma_200 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_200 v0
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
-- Data.Sign.Properties._.IsAbelianGroup.isCommutativeMonoid
d_isCommutativeMonoid_202 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_202 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244 v3
-- Data.Sign.Properties._.IsAbelianGroup.isCommutativeSemigroup
d_isCommutativeSemigroup_204 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_204 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_204 v3
du_isCommutativeSemigroup_204 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_204 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
         (coe v0))
-- Data.Sign.Properties._.IsAbelianGroup.isEquivalence
d_isEquivalence_206 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_206 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))))
-- Data.Sign.Properties._.IsAbelianGroup.isGroup
d_isGroup_208 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_208 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)
-- Data.Sign.Properties._.IsAbelianGroup.isInvertibleMagma
d_isInvertibleMagma_210 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_210 ~v0 ~v1 ~v2 v3
  = du_isInvertibleMagma_210 v3
du_isInvertibleMagma_210 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_210 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Sign.Properties._.IsAbelianGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_212 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_212 ~v0 ~v1 ~v2 v3
  = du_isInvertibleUnitalMagma_212 v3
du_isInvertibleUnitalMagma_212 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_212 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Sign.Properties._.IsAbelianGroup.isMagma
d_isMagma_214 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_214 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))))
-- Data.Sign.Properties._.IsAbelianGroup.isMonoid
d_isMonoid_216 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_216 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0))
-- Data.Sign.Properties._.IsAbelianGroup.isPartialEquivalence
d_isPartialEquivalence_218 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_218 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_218 v3
du_isPartialEquivalence_218 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_218 v0
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
-- Data.Sign.Properties._.IsAbelianGroup.isSemigroup
d_isSemigroup_220 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_220 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0)))
-- Data.Sign.Properties._.IsAbelianGroup.isUnitalMagma
d_isUnitalMagma_222 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_222 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_222 v3
du_isUnitalMagma_222 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_222 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v1)))
-- Data.Sign.Properties._.IsAbelianGroup.refl
d_refl_224 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_224 = erased
-- Data.Sign.Properties._.IsAbelianGroup.reflexive
d_reflexive_226 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_226 = erased
-- Data.Sign.Properties._.IsAbelianGroup.setoid
d_setoid_228 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_228 ~v0 ~v1 ~v2 v3 = du_setoid_228 v3
du_setoid_228 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_228 v0
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
-- Data.Sign.Properties._.IsAbelianGroup.sym
d_sym_230 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_230 = erased
-- Data.Sign.Properties._.IsAbelianGroup.trans
d_trans_232 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_232 = erased
-- Data.Sign.Properties._.IsAbelianGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_234 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_234 = erased
-- Data.Sign.Properties._.IsAbelianGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_236 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_236 = erased
-- Data.Sign.Properties._.IsAbelianGroup.⁻¹-cong
d_'8315''185''45'cong_238 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_238 = erased
-- Data.Sign.Properties._.IsAbelianGroup.∙-cong
d_'8729''45'cong_240 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_240 = erased
-- Data.Sign.Properties._.IsAbelianGroup.∙-congʳ
d_'8729''45'cong'691'_242 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_242 = erased
-- Data.Sign.Properties._.IsAbelianGroup.∙-congˡ
d_'8729''45'cong'737'_244 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_244 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.alter
d_alter_248 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_248 v0
  = coe MAlonzo.Code.Algebra.Structures.d_alter_300 (coe v0)
-- Data.Sign.Properties._.IsAlternativeMagma.alternativeʳ
d_alternative'691'_250 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'691'_250 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.alternativeˡ
d_alternative'737'_252 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alternative'737'_252 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.isEquivalence
d_isEquivalence_254 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_254 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0))
-- Data.Sign.Properties._.IsAlternativeMagma.isMagma
d_isMagma_256 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_256 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0)
-- Data.Sign.Properties._.IsAlternativeMagma.isPartialEquivalence
d_isPartialEquivalence_258 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_258 ~v0 v1 = du_isPartialEquivalence_258 v1
du_isPartialEquivalence_258 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_258 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsAlternativeMagma.refl
d_refl_260 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_260 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.reflexive
d_reflexive_262 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_262 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.setoid
d_setoid_264 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_264 ~v0 v1 = du_setoid_264 v1
du_setoid_264 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_264 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_298 (coe v0))
-- Data.Sign.Properties._.IsAlternativeMagma.sym
d_sym_266 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_266 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.trans
d_trans_268 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_268 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.∙-cong
d_'8729''45'cong_270 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_270 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.∙-congʳ
d_'8729''45'cong'691'_272 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_272 = erased
-- Data.Sign.Properties._.IsAlternativeMagma.∙-congˡ
d_'8729''45'cong'737'_274 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_290 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_274 = erased
-- Data.Sign.Properties._.IsBand.assoc
d_assoc_278 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_278 = erased
-- Data.Sign.Properties._.IsBand.idem
d_idem_280 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_280 = erased
-- Data.Sign.Properties._.IsBand.isEquivalence
d_isEquivalence_282 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_282 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)))
-- Data.Sign.Properties._.IsBand.isMagma
d_isMagma_284 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_284 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0))
-- Data.Sign.Properties._.IsBand.isPartialEquivalence
d_isPartialEquivalence_286 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_286 ~v0 v1 = du_isPartialEquivalence_286 v1
du_isPartialEquivalence_286 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_286 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Sign.Properties._.IsBand.isSemigroup
d_isSemigroup_288 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_288 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)
-- Data.Sign.Properties._.IsBand.refl
d_refl_290 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_290 = erased
-- Data.Sign.Properties._.IsBand.reflexive
d_reflexive_292 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_292 = erased
-- Data.Sign.Properties._.IsBand.setoid
d_setoid_294 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_294 ~v0 v1 = du_setoid_294 v1
du_setoid_294 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_294 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Sign.Properties._.IsBand.sym
d_sym_296 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_296 = erased
-- Data.Sign.Properties._.IsBand.trans
d_trans_298 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_298 = erased
-- Data.Sign.Properties._.IsBand.∙-cong
d_'8729''45'cong_300 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_300 = erased
-- Data.Sign.Properties._.IsBand.∙-congʳ
d_'8729''45'cong'691'_302 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_302 = erased
-- Data.Sign.Properties._.IsBand.∙-congˡ
d_'8729''45'cong'737'_304 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_304 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-assoc
d_'42''45'assoc_308 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_308 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-cancelʳ-nonZero
d_'42''45'cancel'691''45'nonZero_310 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'691''45'nonZero_310 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_312 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45'nonZero_312 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-comm
d_'42''45'comm_314 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_314 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-cong
d_'42''45'cong_316 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_316 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_318 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_318 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_320 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_320 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-identity
d_'42''45'identity_322 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_322 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.identityʳ
d_identity'691'_324 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_324 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.identityˡ
d_identity'737'_326 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_326 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_328 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_328 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_328 v4
du_isCommutativeMagma_328 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_328 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_330 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_330 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeMonoid_330 v4
du_'42''45'isCommutativeMonoid_330 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_330 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_332 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_332 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeSemigroup_332 v4
du_'42''45'isCommutativeSemigroup_332 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_332 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
            (coe v1)))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-isMagma
d_'42''45'isMagma_334 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_334 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_334 v4
du_'42''45'isMagma_334 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_334 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-isMonoid
d_'42''45'isMonoid_336 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_336 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_336 v4
du_'42''45'isMonoid_336 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_336 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.*-isSemigroup
d_'42''45'isSemigroup_338 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_338 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_338 v4
du_'42''45'isSemigroup_338 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_338 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.assoc
d_assoc_340 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_340 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.comm
d_comm_342 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_342 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.∙-cong
d_'8729''45'cong_344 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_344 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_346 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_346 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_348 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_348 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.identity
d_identity_350 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_350 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.identityʳ
d_identity'691'_352 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_352 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.identityˡ
d_identity'737'_354 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_354 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_356 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_356 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_356 v4
du_isCommutativeMagma_356 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_356 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_358 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_358 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_360 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_360 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_360 v4
du_isCommutativeSemigroup_360 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_360 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isMagma
d_isMagma_362 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_362 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isMonoid
d_isMonoid_364 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_364 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isSemigroup
d_isSemigroup_366 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_366 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isUnitalMagma
d_isUnitalMagma_368 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_368 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_368 v4
du_isUnitalMagma_368 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_368 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.distrib
d_distrib_370 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_370 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
               (coe v0))))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.distribʳ
d_distrib'691'_372 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_372 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.distribˡ
d_distrib'737'_374 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_374 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_376 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_376 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
      (coe v0)
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_378 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_378 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemiringWithoutOne_378 v4
du_isCommutativeSemiringWithoutOne_378 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_378 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isEquivalence
d_isEquivalence_380 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_380 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isNearSemiring
d_isNearSemiring_382 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_382 ~v0 ~v1 ~v2 ~v3 v4 = du_isNearSemiring_382 v4
du_isNearSemiring_382 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_382 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isPartialEquivalence
d_isPartialEquivalence_384 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_384 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_384 v4
du_isPartialEquivalence_384 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_384 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isSemiring
d_isSemiring_386 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_386 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
         (coe v0))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_388 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_388 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
            (coe v0)))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_390 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_390 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_390 v4
du_isSemiringWithoutOne_390 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_390 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v1)))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.refl
d_refl_392 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_392 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.reflexive
d_reflexive_394 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_394 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.setoid
d_setoid_396 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_396 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_396 v4
du_setoid_396 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_396 v0
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
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.sym
d_sym_398 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_398 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.trans
d_trans_400 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_400 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.zero
d_zero_402 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_402 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1764
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1886
            (coe v0)))
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.zeroʳ
d_zero'691'_404 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_404 = erased
-- Data.Sign.Properties._.IsCancellativeCommutativeSemiring.zeroˡ
d_zero'737'_406 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1872 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_406 = erased
-- Data.Sign.Properties._.IsCommutativeBand.assoc
d_assoc_410 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_410 = erased
-- Data.Sign.Properties._.IsCommutativeBand.comm
d_comm_412 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_412 = erased
-- Data.Sign.Properties._.IsCommutativeBand.idem
d_idem_414 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_414 = erased
-- Data.Sign.Properties._.IsCommutativeBand.isBand
d_isBand_416 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_416 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)
-- Data.Sign.Properties._.IsCommutativeBand.isCommutativeMagma
d_isCommutativeMagma_418 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_418 ~v0 v1 = du_isCommutativeMagma_418 v1
du_isCommutativeMagma_418 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_418 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_654
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeBand.isCommutativeSemigroup
d_isCommutativeSemigroup_420 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_420 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_654 v1
-- Data.Sign.Properties._.IsCommutativeBand.isEquivalence
d_isEquivalence_422 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_422 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))))
-- Data.Sign.Properties._.IsCommutativeBand.isMagma
d_isMagma_424 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_424 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0)))
-- Data.Sign.Properties._.IsCommutativeBand.isPartialEquivalence
d_isPartialEquivalence_426 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_426 ~v0 v1 = du_isPartialEquivalence_426 v1
du_isPartialEquivalence_426 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_426 v0
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
-- Data.Sign.Properties._.IsCommutativeBand.isSemigroup
d_isSemigroup_428 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_428 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0))
-- Data.Sign.Properties._.IsCommutativeBand.refl
d_refl_430 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_430 = erased
-- Data.Sign.Properties._.IsCommutativeBand.reflexive
d_reflexive_432 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_432 = erased
-- Data.Sign.Properties._.IsCommutativeBand.setoid
d_setoid_434 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_434 ~v0 v1 = du_setoid_434 v1
du_setoid_434 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_434 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Sign.Properties._.IsCommutativeBand.sym
d_sym_436 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_436 = erased
-- Data.Sign.Properties._.IsCommutativeBand.trans
d_trans_438 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_438 = erased
-- Data.Sign.Properties._.IsCommutativeBand.∙-cong
d_'8729''45'cong_440 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_440 = erased
-- Data.Sign.Properties._.IsCommutativeBand.∙-congʳ
d_'8729''45'cong'691'_442 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_442 = erased
-- Data.Sign.Properties._.IsCommutativeBand.∙-congˡ
d_'8729''45'cong'737'_444 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_444 = erased
-- Data.Sign.Properties._.IsCommutativeMagma.comm
d_comm_448 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_448 = erased
-- Data.Sign.Properties._.IsCommutativeMagma.isEquivalence
d_isEquivalence_450 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_450 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0))
-- Data.Sign.Properties._.IsCommutativeMagma.isMagma
d_isMagma_452 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_452 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0)
-- Data.Sign.Properties._.IsCommutativeMagma.isPartialEquivalence
d_isPartialEquivalence_454 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_454 ~v0 v1 = du_isPartialEquivalence_454 v1
du_isPartialEquivalence_454 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_454 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsCommutativeMagma.refl
d_refl_456 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_456 = erased
-- Data.Sign.Properties._.IsCommutativeMagma.reflexive
d_reflexive_458 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_458 = erased
-- Data.Sign.Properties._.IsCommutativeMagma.setoid
d_setoid_460 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_460 ~v0 v1 = du_setoid_460 v1
du_setoid_460 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_460 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_222 (coe v0))
-- Data.Sign.Properties._.IsCommutativeMagma.sym
d_sym_462 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_462 = erased
-- Data.Sign.Properties._.IsCommutativeMagma.trans
d_trans_464 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_464 = erased
-- Data.Sign.Properties._.IsCommutativeMagma.∙-cong
d_'8729''45'cong_466 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_466 = erased
-- Data.Sign.Properties._.IsCommutativeMagma.∙-congʳ
d_'8729''45'cong'691'_468 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_468 = erased
-- Data.Sign.Properties._.IsCommutativeMagma.∙-congˡ
d_'8729''45'cong'737'_470 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_470 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.assoc
d_assoc_474 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_474 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.comm
d_comm_476 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_476 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.identity
d_identity_478 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_478 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Sign.Properties._.IsCommutativeMonoid.identityʳ
d_identity'691'_480 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_480 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.identityˡ
d_identity'737'_482 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_482 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_484 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_484 ~v0 ~v1 v2 = du_isCommutativeMagma_484 v2
du_isCommutativeMagma_484 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_484 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_486 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_486 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814 v2
-- Data.Sign.Properties._.IsCommutativeMonoid.isEquivalence
d_isEquivalence_488 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_488 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))))
-- Data.Sign.Properties._.IsCommutativeMonoid.isMagma
d_isMagma_490 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_490 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)))
-- Data.Sign.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_492 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_492 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0)
-- Data.Sign.Properties._.IsCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_494 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_494 ~v0 ~v1 v2
  = du_isPartialEquivalence_494 v2
du_isPartialEquivalence_494 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_494 v0
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
-- Data.Sign.Properties._.IsCommutativeMonoid.isSemigroup
d_isSemigroup_496 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_496 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Sign.Properties._.IsCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_498 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_498 ~v0 ~v1 v2 = du_isUnitalMagma_498 v2
du_isUnitalMagma_498 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_498 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0))
-- Data.Sign.Properties._.IsCommutativeMonoid.refl
d_refl_500 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_500 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.reflexive
d_reflexive_502 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_502 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.setoid
d_setoid_504 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_504 ~v0 ~v1 v2 = du_setoid_504 v2
du_setoid_504 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_504 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Sign.Properties._.IsCommutativeMonoid.sym
d_sym_506 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_506 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.trans
d_trans_508 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_508 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.∙-cong
d_'8729''45'cong_510 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_510 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_512 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_512 = erased
-- Data.Sign.Properties._.IsCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_514 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_514 = erased
-- Data.Sign.Properties._.IsCommutativeRing._//_
d__'47''47'__518 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
d__'47''47'__518 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__518 v0 v2
du__'47''47'__518 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
du__'47''47'__518 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Sign.Properties._.IsCommutativeRing.*-assoc
d_'42''45'assoc_520 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_520 = erased
-- Data.Sign.Properties._.IsCommutativeRing.*-comm
d_'42''45'comm_522 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_522 = erased
-- Data.Sign.Properties._.IsCommutativeRing.*-cong
d_'42''45'cong_524 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_524 = erased
-- Data.Sign.Properties._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_526 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_526 = erased
-- Data.Sign.Properties._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_528 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_528 = erased
-- Data.Sign.Properties._.IsCommutativeRing.*-identity
d_'42''45'identity_530 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_530 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Sign.Properties._.IsCommutativeRing.identityʳ
d_identity'691'_532 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_532 = erased
-- Data.Sign.Properties._.IsCommutativeRing.identityˡ
d_identity'737'_534 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_534 = erased
-- Data.Sign.Properties._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_536 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_536 v0 v1 v2 v3 ~v4 v5
  = du_isCommutativeMagma_536 v0 v1 v2 v3 v5
du_isCommutativeMagma_536 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_536 v0 v1 v2 v3 v4
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
-- Data.Sign.Properties._.IsCommutativeRing.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_538 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_538 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isCommutativeMonoid_538 v0 v1 v2 v3 v5
du_'42''45'isCommutativeMonoid_538 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'42''45'isCommutativeMonoid_538 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Sign.Properties._.IsCommutativeRing.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_540 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_540 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isCommutativeSemigroup_540 v0 v1 v2 v3 v5
du_'42''45'isCommutativeSemigroup_540 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_540 v0 v1 v2 v3 v4
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
-- Data.Sign.Properties._.IsCommutativeRing.*-isMagma
d_'42''45'isMagma_542 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_542 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMagma_542 v0 v1 v2 v3 v5
du_'42''45'isMagma_542 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_542 v0 v1 v2 v3 v4
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
-- Data.Sign.Properties._.IsCommutativeRing.*-isMonoid
d_'42''45'isMonoid_544 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_544 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMonoid_544 v0 v1 v2 v3 v5
du_'42''45'isMonoid_544 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_544 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2860 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4))
-- Data.Sign.Properties._.IsCommutativeRing.*-isSemigroup
d_'42''45'isSemigroup_546 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_546 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isSemigroup_546 v0 v1 v2 v3 v5
du_'42''45'isSemigroup_546 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_546 v0 v1 v2 v3 v4
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
-- Data.Sign.Properties._.IsCommutativeRing.assoc
d_assoc_548 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_548 = erased
-- Data.Sign.Properties._.IsCommutativeRing.comm
d_comm_550 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_550 = erased
-- Data.Sign.Properties._.IsCommutativeRing.∙-cong
d_'8729''45'cong_552 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_552 = erased
-- Data.Sign.Properties._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_554 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_554 = erased
-- Data.Sign.Properties._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_556 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_556 = erased
-- Data.Sign.Properties._.IsCommutativeRing.identity
d_identity_558 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_558 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_558 v5
du_identity_558 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_558 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.identityʳ
d_identity'691'_560 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_560 = erased
-- Data.Sign.Properties._.IsCommutativeRing.identityˡ
d_identity'737'_562 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_562 = erased
-- Data.Sign.Properties._.IsCommutativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_564 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_564 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Sign.Properties._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_566 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_566 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_566 v5
du_isCommutativeMagma_566 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_566 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isCommutativeMonoid
d_isCommutativeMonoid_568 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_568 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_568 v5
du_isCommutativeMonoid_568 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_568 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_570 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_570 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_570 v5
du_isCommutativeSemigroup_570 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_570 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isGroup
d_isGroup_572 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_572 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_572 v5
du_isGroup_572 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
du_isGroup_572 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v1)))
-- Data.Sign.Properties._.IsCommutativeRing.isInvertibleMagma
d_isInvertibleMagma_574 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_574 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_574 v5
du_isInvertibleMagma_574 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_574 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_576 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_576 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_576 v5
du_isInvertibleUnitalMagma_576 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_576 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isMagma
d_isMagma_578 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_578 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_578 v5
du_isMagma_578 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_578 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isMonoid
d_isMonoid_580 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_580 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_580 v5
du_isMonoid_580 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_isMonoid_580 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isSemigroup
d_isSemigroup_582 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_582 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_582 v5
du_isSemigroup_582 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_582 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isUnitalMagma
d_isUnitalMagma_584 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_584 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_584 v5
du_isUnitalMagma_584 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_584 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.⁻¹-cong
d_'8315''185''45'cong_586 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_586 = erased
-- Data.Sign.Properties._.IsCommutativeRing.inverse
d_inverse_588 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_588 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_588 v5
du_inverse_588 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_588 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.inverseʳ
d_inverse'691'_590 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_590 = erased
-- Data.Sign.Properties._.IsCommutativeRing.inverseˡ
d_inverse'737'_592 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_592 = erased
-- Data.Sign.Properties._.IsCommutativeRing.distrib
d_distrib_594 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_594 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2770
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Sign.Properties._.IsCommutativeRing.distribʳ
d_distrib'691'_596 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_596 = erased
-- Data.Sign.Properties._.IsCommutativeRing.distribˡ
d_distrib'737'_598 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_598 = erased
-- Data.Sign.Properties._.IsCommutativeRing.isCommutativeSemiring
d_isCommutativeSemiring_600 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_isCommutativeSemiring_600 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018 v0 v1
      v2 v3 v5
-- Data.Sign.Properties._.IsCommutativeRing.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_602 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_602 v0 v1 v2 v3 ~v4 v5
  = du_isCommutativeSemiringWithoutOne_602 v0 v1 v2 v3 v5
du_isCommutativeSemiringWithoutOne_602 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
du_isCommutativeSemiringWithoutOne_602 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_3018
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Sign.Properties._.IsCommutativeRing.isEquivalence
d_isEquivalence_604 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_604 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_604 v5
du_isEquivalence_604 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_604 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isNearSemiring
d_isNearSemiring_606 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_606 v0 v1 v2 v3 ~v4 v5
  = du_isNearSemiring_606 v0 v1 v2 v3 v5
du_isNearSemiring_606 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_606 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v5)))
-- Data.Sign.Properties._.IsCommutativeRing.isPartialEquivalence
d_isPartialEquivalence_608 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_608 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_608 v5
du_isPartialEquivalence_608 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_608 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.isRing
d_isRing_610 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740
d_isRing_610 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0)
-- Data.Sign.Properties._.IsCommutativeRing.isRingWithoutOne
d_isRingWithoutOne_612 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
d_isRingWithoutOne_612 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isRingWithoutOne_612 v5
du_isRingWithoutOne_612 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
du_isRingWithoutOne_612 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Sign.Properties._.IsCommutativeRing.isSemiring
d_isSemiring_614 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_614 v0 v1 v2 v3 ~v4 v5
  = du_isSemiring_614 v0 v1 v2 v3 v5
du_isSemiring_614 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
du_isSemiring_614 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4))
-- Data.Sign.Properties._.IsCommutativeRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_616 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_616 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isSemiringWithoutAnnihilatingZero_616 v5
du_isSemiringWithoutAnnihilatingZero_616 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
du_isSemiringWithoutAnnihilatingZero_616 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2868
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v0))
-- Data.Sign.Properties._.IsCommutativeRing.isSemiringWithoutOne
d_isSemiringWithoutOne_618 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_618 v0 v1 v2 v3 ~v4 v5
  = du_isSemiringWithoutOne_618 v0 v1 v2 v3 v5
du_isSemiringWithoutOne_618 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_618 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Data.Sign.Properties._.IsCommutativeRing.refl
d_refl_620 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_620 = erased
-- Data.Sign.Properties._.IsCommutativeRing.reflexive
d_reflexive_622 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_622 = erased
-- Data.Sign.Properties._.IsCommutativeRing.setoid
d_setoid_624 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_624 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_624 v5
du_setoid_624 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_624 v0
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
-- Data.Sign.Properties._.IsCommutativeRing.sym
d_sym_626 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_626 = erased
-- Data.Sign.Properties._.IsCommutativeRing.trans
d_trans_628 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_628 = erased
-- Data.Sign.Properties._.IsCommutativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_630 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_630 = erased
-- Data.Sign.Properties._.IsCommutativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_632 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_632 = erased
-- Data.Sign.Properties._.IsCommutativeRing.zero
d_zero_634 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_634 v0 v1 v2 v3 ~v4 v5 = du_zero_634 v0 v1 v2 v3 v5
du_zero_634 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_634 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2904 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero_2468 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v5)))
-- Data.Sign.Properties._.IsCommutativeRing.zeroʳ
d_zero'691'_636 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_636 = erased
-- Data.Sign.Properties._.IsCommutativeRing.zeroˡ
d_zero'737'_638 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2888 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_638 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.assoc
d_assoc_642 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_642 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.comm
d_comm_644 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_644 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.isCommutativeMagma
d_isCommutativeMagma_646 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_646 v0 v1
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606 v1
-- Data.Sign.Properties._.IsCommutativeSemigroup.isEquivalence
d_isEquivalence_648 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_648 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)))
-- Data.Sign.Properties._.IsCommutativeSemigroup.isMagma
d_isMagma_650 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_650 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemigroup.isPartialEquivalence
d_isPartialEquivalence_652 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_652 ~v0 v1 = du_isPartialEquivalence_652 v1
du_isPartialEquivalence_652 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_652 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Sign.Properties._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_654 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_654 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)
-- Data.Sign.Properties._.IsCommutativeSemigroup.refl
d_refl_656 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_656 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.reflexive
d_reflexive_658 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_658 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.setoid
d_setoid_660 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_660 ~v0 v1 = du_setoid_660 v1
du_setoid_660 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_660 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Sign.Properties._.IsCommutativeSemigroup.sym
d_sym_662 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_662 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.trans
d_trans_664 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_664 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.∙-cong
d_'8729''45'cong_666 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_666 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.∙-congʳ
d_'8729''45'cong'691'_668 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_668 = erased
-- Data.Sign.Properties._.IsCommutativeSemigroup.∙-congˡ
d_'8729''45'cong'737'_670 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_670 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.*-assoc
d_'42''45'assoc_674 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_674 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.*-comm
d_'42''45'comm_676 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_676 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.*-cong
d_'42''45'cong_678 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_678 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_680 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_680 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_682 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_682 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.*-identity
d_'42''45'identity_684 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_684 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Sign.Properties._.IsCommutativeSemiring.identityʳ
d_identity'691'_686 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_686 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.identityˡ
d_identity'737'_688 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_688 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_690 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_690 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_690 v4
du_isCommutativeMagma_690 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_690 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiring.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_692 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_692 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1860
      v4
-- Data.Sign.Properties._.IsCommutativeSemiring.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_694 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_694 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isCommutativeSemigroup_694 v4
du_'42''45'isCommutativeSemigroup_694 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'42''45'isCommutativeSemigroup_694 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiring.*-isMagma
d_'42''45'isMagma_696 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_696 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_696 v4
du_'42''45'isMagma_696 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_696 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Sign.Properties._.IsCommutativeSemiring.*-isMonoid
d_'42''45'isMonoid_698 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_698 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_698 v4
du_'42''45'isMonoid_698 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_698 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Sign.Properties._.IsCommutativeSemiring.*-isSemigroup
d_'42''45'isSemigroup_700 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_700 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_700 v4
du_'42''45'isSemigroup_700 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_700 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Sign.Properties._.IsCommutativeSemiring.assoc
d_assoc_702 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_702 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.comm
d_comm_704 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_704 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.∙-cong
d_'8729''45'cong_706 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_706 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.∙-congʳ
d_'8729''45'cong'691'_708 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_708 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.∙-congˡ
d_'8729''45'cong'737'_710 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_710 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.identity
d_identity_712 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_712 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))))
-- Data.Sign.Properties._.IsCommutativeSemiring.identityʳ
d_identity'691'_714 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_714 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.identityˡ
d_identity'737'_716 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_716 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.isCommutativeMagma
d_isCommutativeMagma_718 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_718 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_718 v4
du_isCommutativeMagma_718 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_718 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_720 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_720 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Sign.Properties._.IsCommutativeSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_722 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_722 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_722 v4
du_isCommutativeSemigroup_722 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_722 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiring.isMagma
d_isMagma_724 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_724 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiring.isMonoid
d_isMonoid_726 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_726 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))))
-- Data.Sign.Properties._.IsCommutativeSemiring.isSemigroup
d_isSemigroup_728 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_728 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))))
-- Data.Sign.Properties._.IsCommutativeSemiring.isUnitalMagma
d_isUnitalMagma_730 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_730 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_730 v4
du_isUnitalMagma_730 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_730 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiring.distrib
d_distrib_732 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_732 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)))
-- Data.Sign.Properties._.IsCommutativeSemiring.distribʳ
d_distrib'691'_734 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_734 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.distribˡ
d_distrib'737'_736 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_736 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_738 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438
d_isCommutativeSemiringWithoutOne_738 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1852
      v4
-- Data.Sign.Properties._.IsCommutativeSemiring.isEquivalence
d_isEquivalence_740 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_740 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiring.isNearSemiring
d_isNearSemiring_742 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_742 ~v0 ~v1 ~v2 ~v3 v4 = du_isNearSemiring_742 v4
du_isNearSemiring_742 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_742 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
            (coe v1)))
-- Data.Sign.Properties._.IsCommutativeSemiring.isPartialEquivalence
d_isPartialEquivalence_744 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_744 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_744 v4
du_isPartialEquivalence_744 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_744 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiring.isSemiring
d_isSemiring_746 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_746 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0)
-- Data.Sign.Properties._.IsCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_748 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_748 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_750 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_750 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_750 v4
du_isSemiringWithoutOne_750 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_750 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiring.refl
d_refl_752 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_752 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.reflexive
d_reflexive_754 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_754 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.setoid
d_setoid_756 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_756 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_756 v4
du_setoid_756 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_756 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiring.sym
d_sym_758 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_758 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.trans
d_trans_760 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_760 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.zero
d_zero_762 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_762 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1764 (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiring.zeroʳ
d_zero'691'_764 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_764 = erased
-- Data.Sign.Properties._.IsCommutativeSemiring.zeroˡ
d_zero'737'_766 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_766 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.*-assoc
d_'42''45'assoc_770 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_770 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_772 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_772 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.*-cong
d_'42''45'cong_774 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_774 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_776 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_776 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_778 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_778 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_780 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_780 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_780 v3
du_isCommutativeMagma_780 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_780 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_782 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_782 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1520
      v3
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_784 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_784 ~v0 ~v1 ~v2 v3 = du_'42''45'isMagma_784 v3
du_'42''45'isMagma_784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_784 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1410
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_786 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_786 ~v0 ~v1 ~v2 v3
  = du_'42''45'isSemigroup_786 v3
du_'42''45'isSemigroup_786 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_786 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1412
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.assoc
d_assoc_788 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_788 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.comm
d_comm_790 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_790 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.∙-cong
d_'8729''45'cong_792 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_792 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_794 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_794 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_796 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_796 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.identity
d_identity_798 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_798 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
               (coe v0))))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.identityʳ
d_identity'691'_800 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_800 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.identityˡ
d_identity'737'_802 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_802 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_804 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_804 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_804 v3
du_isCommutativeMagma_804 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_804 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_806 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_806 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_808 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_808 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_808 v3
du_isCommutativeSemigroup_808 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_808 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe v1)))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.isMonoid
d_isMonoid_810 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_810 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
            (coe v0)))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.distrib
d_distrib_812 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_812 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1366
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.distribʳ
d_distrib'691'_814 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_814 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.distribˡ
d_distrib'737'_816 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_816 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.isEquivalence
d_isEquivalence_818 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_818 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.isNearSemiring
d_isNearSemiring_820 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_820 ~v0 ~v1 ~v2 v3 = du_isNearSemiring_820 v3
du_isNearSemiring_820 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_820 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.isPartialEquivalence
d_isPartialEquivalence_822 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_822 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_822 v3
du_isPartialEquivalence_822 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_822 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_824 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_824 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
      (coe v0)
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.refl
d_refl_826 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_826 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.reflexive
d_reflexive_828 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_828 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.setoid
d_setoid_830 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_830 ~v0 ~v1 ~v2 v3 = du_setoid_830 v3
du_setoid_830 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_830 v0
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
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.sym
d_sym_832 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_832 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.trans
d_trans_834 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_834 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.zero
d_zero_836 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_836 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1368
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1450
         (coe v0))
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.zeroʳ
d_zero'691'_838 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_838 = erased
-- Data.Sign.Properties._.IsCommutativeSemiringWithoutOne.zeroˡ
d_zero'737'_840 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1438 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_840 = erased
-- Data.Sign.Properties._.IsFlexibleMagma.flex
d_flex_844 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flex_844 = erased
-- Data.Sign.Properties._.IsFlexibleMagma.isEquivalence
d_isEquivalence_846 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_846 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0))
-- Data.Sign.Properties._.IsFlexibleMagma.isMagma
d_isMagma_848 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_848 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0)
-- Data.Sign.Properties._.IsFlexibleMagma.isPartialEquivalence
d_isPartialEquivalence_850 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_850 ~v0 v1 = du_isPartialEquivalence_850 v1
du_isPartialEquivalence_850 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_850 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsFlexibleMagma.refl
d_refl_852 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_852 = erased
-- Data.Sign.Properties._.IsFlexibleMagma.reflexive
d_reflexive_854 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_854 = erased
-- Data.Sign.Properties._.IsFlexibleMagma.setoid
d_setoid_856 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_856 ~v0 v1 = du_setoid_856 v1
du_setoid_856 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_856 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_340 (coe v0))
-- Data.Sign.Properties._.IsFlexibleMagma.sym
d_sym_858 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_858 = erased
-- Data.Sign.Properties._.IsFlexibleMagma.trans
d_trans_860 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_860 = erased
-- Data.Sign.Properties._.IsFlexibleMagma.∙-cong
d_'8729''45'cong_862 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_862 = erased
-- Data.Sign.Properties._.IsFlexibleMagma.∙-congʳ
d_'8729''45'cong'691'_864 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_864 = erased
-- Data.Sign.Properties._.IsFlexibleMagma.∙-congˡ
d_'8729''45'cong'737'_866 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_332 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_866 = erased
-- Data.Sign.Properties._.IsGroup._-_
d__'45'__870 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
d__'45'__870 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du__'45'__1142 v0 v2
-- Data.Sign.Properties._.IsGroup._//_
d__'47''47'__872 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
d__'47''47'__872 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 v0 v2 v4 v5
-- Data.Sign.Properties._.IsGroup._\\_
d__'92''92'__874 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
d__'92''92'__874 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du__'92''92'__1130 v0 v2 v4 v5
-- Data.Sign.Properties._.IsGroup.assoc
d_assoc_876 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_876 = erased
-- Data.Sign.Properties._.IsGroup.identity
d_identity_878 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_878 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Sign.Properties._.IsGroup.identityʳ
d_identity'691'_880 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_880 = erased
-- Data.Sign.Properties._.IsGroup.identityˡ
d_identity'737'_882 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_882 = erased
-- Data.Sign.Properties._.IsGroup.inverse
d_inverse_884 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_884 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1090 (coe v0)
-- Data.Sign.Properties._.IsGroup.inverseʳ
d_inverse'691'_886 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_886 = erased
-- Data.Sign.Properties._.IsGroup.inverseˡ
d_inverse'737'_888 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_888 = erased
-- Data.Sign.Properties._.IsGroup.isEquivalence
d_isEquivalence_890 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_890 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))))
-- Data.Sign.Properties._.IsGroup.isInvertibleMagma
d_isInvertibleMagma_892 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_892 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160 v3
-- Data.Sign.Properties._.IsGroup.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_894 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_894 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162 v3
-- Data.Sign.Properties._.IsGroup.isMagma
d_isMagma_896 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_896 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)))
-- Data.Sign.Properties._.IsGroup.isMonoid
d_isMonoid_898 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_898 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0)
-- Data.Sign.Properties._.IsGroup.isPartialEquivalence
d_isPartialEquivalence_900 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_900 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_900 v3
du_isPartialEquivalence_900 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_900 v0
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
-- Data.Sign.Properties._.IsGroup.isSemigroup
d_isSemigroup_902 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_902 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Sign.Properties._.IsGroup.isUnitalMagma
d_isUnitalMagma_904 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_904 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_904 v3
du_isUnitalMagma_904 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_904 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0))
-- Data.Sign.Properties._.IsGroup.refl
d_refl_906 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_906 = erased
-- Data.Sign.Properties._.IsGroup.reflexive
d_reflexive_908 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_908 = erased
-- Data.Sign.Properties._.IsGroup.setoid
d_setoid_910 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_910 ~v0 ~v1 ~v2 v3 = du_setoid_910 v3
du_setoid_910 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_910 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_1088 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Sign.Properties._.IsGroup.sym
d_sym_912 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_912 = erased
-- Data.Sign.Properties._.IsGroup.trans
d_trans_914 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_914 = erased
-- Data.Sign.Properties._.IsGroup.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_916 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_916 = erased
-- Data.Sign.Properties._.IsGroup.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_918 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_918 = erased
-- Data.Sign.Properties._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_920 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_920 = erased
-- Data.Sign.Properties._.IsGroup.∙-cong
d_'8729''45'cong_922 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_922 = erased
-- Data.Sign.Properties._.IsGroup.∙-congʳ
d_'8729''45'cong'691'_924 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_924 = erased
-- Data.Sign.Properties._.IsGroup.∙-congˡ
d_'8729''45'cong'737'_926 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_926 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.assoc
d_assoc_930 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_930 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.comm
d_comm_932 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_932 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.idem
d_idem_934 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_934 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.identity
d_identity_936 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_936 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.identityʳ
d_identity'691'_938 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_938 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.identityˡ
d_identity'737'_940 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_940 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isBand
d_isBand_942 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_942 ~v0 ~v1 v2 = du_isBand_942 v2
du_isBand_942 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_942 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isBand_876
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v0))
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isCommutativeBand
d_isCommutativeBand_944 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_944 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 v2
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMagma
d_isCommutativeMagma_946 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_946 ~v0 ~v1 v2 = du_isCommutativeMagma_946 v2
du_isCommutativeMagma_946 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_946 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_948 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_948 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0)
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isCommutativeSemigroup
d_isCommutativeSemigroup_950 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_950 ~v0 ~v1 v2
  = du_isCommutativeSemigroup_950 v2
du_isCommutativeSemigroup_950 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_950 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isEquivalence
d_isEquivalence_952 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_952 v0
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
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isIdempotentMonoid
d_isIdempotentMonoid_954 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_954 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 v2
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isMagma
d_isMagma_956 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_956 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
               (coe v0))))
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isMonoid
d_isMonoid_958 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_958 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894 (coe v0))
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isPartialEquivalence
d_isPartialEquivalence_960 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_960 ~v0 ~v1 v2
  = du_isPartialEquivalence_960 v2
du_isPartialEquivalence_960 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_960 v0
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
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isSemigroup
d_isSemigroup_962 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_962 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v0)))
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.isUnitalMagma
d_isUnitalMagma_964 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_964 ~v0 ~v1 v2 = du_isUnitalMagma_964 v2
du_isUnitalMagma_964 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_964 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.refl
d_refl_966 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_966 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.reflexive
d_reflexive_968 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_968 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.setoid
d_setoid_970 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_970 ~v0 ~v1 v2 = du_setoid_970 v2
du_setoid_970 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_970 v0
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
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.sym
d_sym_972 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_972 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.trans
d_trans_974 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_974 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.∙-cong
d_'8729''45'cong_976 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_976 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.∙-congʳ
d_'8729''45'cong'691'_978 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_978 = erased
-- Data.Sign.Properties._.IsIdempotentCommutativeMonoid.∙-congˡ
d_'8729''45'cong'737'_980 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_980 = erased
-- Data.Sign.Properties._.IsIdempotentMagma.idem
d_idem_984 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_984 = erased
-- Data.Sign.Properties._.IsIdempotentMagma.isEquivalence
d_isEquivalence_986 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_986 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0))
-- Data.Sign.Properties._.IsIdempotentMagma.isMagma
d_isMagma_988 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_988 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0)
-- Data.Sign.Properties._.IsIdempotentMagma.isPartialEquivalence
d_isPartialEquivalence_990 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_990 ~v0 v1 = du_isPartialEquivalence_990 v1
du_isPartialEquivalence_990 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_990 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsIdempotentMagma.refl
d_refl_992 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_992 = erased
-- Data.Sign.Properties._.IsIdempotentMagma.reflexive
d_reflexive_994 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_994 = erased
-- Data.Sign.Properties._.IsIdempotentMagma.setoid
d_setoid_996 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_996 ~v0 v1 = du_setoid_996 v1
du_setoid_996 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_996 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0))
-- Data.Sign.Properties._.IsIdempotentMagma.sym
d_sym_998 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_998 = erased
-- Data.Sign.Properties._.IsIdempotentMagma.trans
d_trans_1000 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1000 = erased
-- Data.Sign.Properties._.IsIdempotentMagma.∙-cong
d_'8729''45'cong_1002 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1002 = erased
-- Data.Sign.Properties._.IsIdempotentMagma.∙-congʳ
d_'8729''45'cong'691'_1004 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1004 = erased
-- Data.Sign.Properties._.IsIdempotentMagma.∙-congˡ
d_'8729''45'cong'737'_1006 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_252 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1006 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.assoc
d_assoc_1010 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1010 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.idem
d_idem_1012 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1012 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.identity
d_identity_1014 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1014 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Sign.Properties._.IsIdempotentMonoid.identityʳ
d_identity'691'_1016 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1016 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.identityˡ
d_identity'737'_1018 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1018 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.isBand
d_isBand_1020 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1020 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isBand_876 v2
-- Data.Sign.Properties._.IsIdempotentMonoid.isEquivalence
d_isEquivalence_1022 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1022 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))))
-- Data.Sign.Properties._.IsIdempotentMonoid.isMagma
d_isMagma_1024 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1024 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0)))
-- Data.Sign.Properties._.IsIdempotentMonoid.isMonoid
d_isMonoid_1026 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1026 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0)
-- Data.Sign.Properties._.IsIdempotentMonoid.isPartialEquivalence
d_isPartialEquivalence_1028 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1028 ~v0 ~v1 v2
  = du_isPartialEquivalence_1028 v2
du_isPartialEquivalence_1028 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1028 v0
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
-- Data.Sign.Properties._.IsIdempotentMonoid.isSemigroup
d_isSemigroup_1030 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1030 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Sign.Properties._.IsIdempotentMonoid.isUnitalMagma
d_isUnitalMagma_1032 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1032 ~v0 ~v1 v2 = du_isUnitalMagma_1032 v2
du_isUnitalMagma_1032 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1032 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0))
-- Data.Sign.Properties._.IsIdempotentMonoid.refl
d_refl_1034 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1034 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.reflexive
d_reflexive_1036 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1036 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.setoid
d_setoid_1038 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1038 ~v0 ~v1 v2 = du_setoid_1038 v2
du_setoid_1038 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1038 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMonoid_836 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v2))))
-- Data.Sign.Properties._.IsIdempotentMonoid.sym
d_sym_1040 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1040 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.trans
d_trans_1042 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1042 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.∙-cong
d_'8729''45'cong_1044 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1044 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.∙-congʳ
d_'8729''45'cong'691'_1046 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1046 = erased
-- Data.Sign.Properties._.IsIdempotentMonoid.∙-congˡ
d_'8729''45'cong'737'_1048 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1048 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.*-assoc
d_'42''45'assoc_1052 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1052 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.*-cong
d_'42''45'cong_1054 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1054 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.∙-congʳ
d_'8729''45'cong'691'_1056 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1056 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.∙-congˡ
d_'8729''45'cong'737'_1058 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1058 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.*-identity
d_'42''45'identity_1060 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1060 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Sign.Properties._.IsIdempotentSemiring.identityʳ
d_identity'691'_1062 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1062 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.identityˡ
d_identity'737'_1064 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1064 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.*-isMagma
d_'42''45'isMagma_1066 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1066 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_1066 v4
du_'42''45'isMagma_1066 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1066 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Sign.Properties._.IsIdempotentSemiring.*-isMonoid
d_'42''45'isMonoid_1068 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1068 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_1068 v4
du_'42''45'isMonoid_1068 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1068 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Sign.Properties._.IsIdempotentSemiring.*-isSemigroup
d_'42''45'isSemigroup_1070 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1070 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_1070 v4
du_'42''45'isSemigroup_1070 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1070 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v1)))
-- Data.Sign.Properties._.IsIdempotentSemiring.assoc
d_assoc_1072 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1072 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.comm
d_comm_1074 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1074 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.∙-cong
d_'8729''45'cong_1076 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1076 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.∙-congʳ
d_'8729''45'cong'691'_1078 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1078 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.∙-congˡ
d_'8729''45'cong'737'_1080 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1080 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.+-idem
d_'43''45'idem_1082 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1082 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.identity
d_identity_1084 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1084 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))))
-- Data.Sign.Properties._.IsIdempotentSemiring.identityʳ
d_identity'691'_1086 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1086 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.identityˡ
d_identity'737'_1088 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1088 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.isBand
d_isBand_1090 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1090 ~v0 ~v1 ~v2 ~v3 v4 = du_isBand_1090 v4
du_isBand_1090 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1090 v0
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
-- Data.Sign.Properties._.IsIdempotentSemiring.isCommutativeBand
d_isCommutativeBand_1092 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1092 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeBand_1092 v4
du_isCommutativeBand_1092 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_1092 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
      (coe
         MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
         (coe v0))
-- Data.Sign.Properties._.IsIdempotentSemiring.isCommutativeMagma
d_isCommutativeMagma_1094 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1094 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_1094 v4
du_isCommutativeMagma_1094 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1094 v0
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
-- Data.Sign.Properties._.IsIdempotentSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1096 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1096 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Sign.Properties._.IsIdempotentSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_1098 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1098 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_1098 v4
du_isCommutativeSemigroup_1098 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1098 v0
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
-- Data.Sign.Properties._.IsIdempotentSemiring.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_1100 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_1100 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
      v4
-- Data.Sign.Properties._.IsIdempotentSemiring.isIdempotentMonoid
d_isIdempotentMonoid_1102 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1102 ~v0 ~v1 ~v2 ~v3 v4
  = du_isIdempotentMonoid_1102 v4
du_isIdempotentMonoid_1102 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_1102 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
      (coe
         MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
         (coe v0))
-- Data.Sign.Properties._.IsIdempotentSemiring.isMagma
d_isMagma_1104 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1104 v0
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
-- Data.Sign.Properties._.IsIdempotentSemiring.isMonoid
d_isMonoid_1106 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1106 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))))
-- Data.Sign.Properties._.IsIdempotentSemiring.isSemigroup
d_isSemigroup_1108 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1108 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))))
-- Data.Sign.Properties._.IsIdempotentSemiring.isUnitalMagma
d_isUnitalMagma_1110 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1110 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_1110 v4
du_isUnitalMagma_1110 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1110 v0
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
-- Data.Sign.Properties._.IsIdempotentSemiring.distrib
d_distrib_1112 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1112 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)))
-- Data.Sign.Properties._.IsIdempotentSemiring.distribʳ
d_distrib'691'_1114 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1114 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.distribˡ
d_distrib'737'_1116 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1116 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.isEquivalence
d_isEquivalence_1118 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1118 v0
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
-- Data.Sign.Properties._.IsIdempotentSemiring.isNearSemiring
d_isNearSemiring_1120 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_1120 ~v0 ~v1 ~v2 ~v3 v4
  = du_isNearSemiring_1120 v4
du_isNearSemiring_1120 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_1120 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
            (coe v1)))
-- Data.Sign.Properties._.IsIdempotentSemiring.isPartialEquivalence
d_isPartialEquivalence_1122 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1122 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1122 v4
du_isPartialEquivalence_1122 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1122 v0
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
-- Data.Sign.Properties._.IsIdempotentSemiring.isSemiring
d_isSemiring_1124 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_1124 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0)
-- Data.Sign.Properties._.IsIdempotentSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1126 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1126 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Sign.Properties._.IsIdempotentSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_1128 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1128 ~v0 ~v1 ~v2 ~v3 v4
  = du_isSemiringWithoutOne_1128 v4
du_isSemiringWithoutOne_1128 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1128 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Sign.Properties._.IsIdempotentSemiring.refl
d_refl_1130 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1130 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.reflexive
d_reflexive_1132 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1132 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.setoid
d_setoid_1134 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1134 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1134 v4
du_setoid_1134 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1134 v0
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
-- Data.Sign.Properties._.IsIdempotentSemiring.sym
d_sym_1136 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1136 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.trans
d_trans_1138 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1138 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.zero
d_zero_1140 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1140 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v0))
-- Data.Sign.Properties._.IsIdempotentSemiring.zeroʳ
d_zero'691'_1142 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1142 = erased
-- Data.Sign.Properties._.IsIdempotentSemiring.zeroˡ
d_zero'737'_1144 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1144 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.inverse
d_inverse_1148 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1148 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_974 (coe v0)
-- Data.Sign.Properties._.IsInvertibleMagma.inverseʳ
d_inverse'691'_1150 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1150 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.inverseˡ
d_inverse'737'_1152 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1152 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.isEquivalence
d_isEquivalence_1154 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0))
-- Data.Sign.Properties._.IsInvertibleMagma.isMagma
d_isMagma_1156 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1156 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0)
-- Data.Sign.Properties._.IsInvertibleMagma.isPartialEquivalence
d_isPartialEquivalence_1158 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1158 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1158 v3
du_isPartialEquivalence_1158 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1158 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsInvertibleMagma.refl
d_refl_1160 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1160 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.reflexive
d_reflexive_1162 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1162 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.setoid
d_setoid_1164 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1164 ~v0 ~v1 ~v2 v3 = du_setoid_1164 v3
du_setoid_1164 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1164 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v0))
-- Data.Sign.Properties._.IsInvertibleMagma.sym
d_sym_1166 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1166 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.trans
d_trans_1168 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1168 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_1170 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1170 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.∙-cong
d_'8729''45'cong_1172 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1172 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.∙-congʳ
d_'8729''45'cong'691'_1174 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1174 = erased
-- Data.Sign.Properties._.IsInvertibleMagma.∙-congˡ
d_'8729''45'cong'737'_1176 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1176 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.identity
d_identity_1180 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1180 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_1026 (coe v0)
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.identityʳ
d_identity'691'_1182 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1182 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.identityˡ
d_identity'737'_1184 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1184 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.inverse
d_inverse_1186 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1186 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_974
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0))
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.inverseʳ
d_inverse'691'_1188 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1188 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.inverseˡ
d_inverse'737'_1190 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1190 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.isEquivalence
d_isEquivalence_1192 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1192 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_972
         (coe
            MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0)))
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_1194 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1194 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0)
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.isMagma
d_isMagma_1196 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1196 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_972
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024 (coe v0))
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.isPartialEquivalence
d_isPartialEquivalence_1198 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1198 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1198 v3
du_isPartialEquivalence_1198 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1198 v0
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
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.isUnitalMagma
d_isUnitalMagma_1200 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1200 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_1064 v3
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.refl
d_refl_1202 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1202 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.reflexive
d_reflexive_1204 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1204 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.setoid
d_setoid_1206 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1206 ~v0 ~v1 ~v2 v3 = du_setoid_1206 v3
du_setoid_1206 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1206 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_1024
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_972 (coe v1)))
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.sym
d_sym_1208 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1208 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.trans
d_trans_1210 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1210 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.⁻¹-cong
d_'8315''185''45'cong_1212 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1212 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.∙-cong
d_'8729''45'cong_1214 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1214 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.∙-congʳ
d_'8729''45'cong'691'_1216 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1216 = erased
-- Data.Sign.Properties._.IsInvertibleUnitalMagma.∙-congˡ
d_'8729''45'cong'737'_1218 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1218 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.*-assoc
d_'42''45'assoc_1222 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1222 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.*-cong
d_'42''45'cong_1224 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1224 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.∙-congʳ
d_'8729''45'cong'691'_1226 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1226 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.∙-congˡ
d_'8729''45'cong'737'_1228 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1228 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.*-identity
d_'42''45'identity_1230 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1230 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Sign.Properties._.IsKleeneAlgebra.identityʳ
d_identity'691'_1232 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1232 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.identityˡ
d_identity'737'_1234 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1234 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.*-isMagma
d_'42''45'isMagma_1236 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1236 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMagma_1236 v5
du_'42''45'isMagma_1236 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1236 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.*-isMonoid
d_'42''45'isMonoid_1238 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1238 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMonoid_1238 v5
du_'42''45'isMonoid_1238 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1238 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.*-isSemigroup
d_'42''45'isSemigroup_1240 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1240 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isSemigroup_1240 v5
du_'42''45'isSemigroup_1240 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1240 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.assoc
d_assoc_1242 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1242 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.comm
d_comm_1244 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1244 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.∙-cong
d_'8729''45'cong_1246 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1246 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.∙-congʳ
d_'8729''45'cong'691'_1248 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1248 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.∙-congˡ
d_'8729''45'cong'737'_1250 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1250 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.+-idem
d_'43''45'idem_1252 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1252 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.identity
d_identity_1254 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1254 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.identityʳ
d_identity'691'_1256 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1256 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.identityˡ
d_identity'737'_1258 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1258 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.isBand
d_isBand_1260 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_1260 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isBand_1260 v5
du_isBand_1260 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_1260 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.isCommutativeBand
d_isCommutativeBand_1262 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_1262 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeBand_1262 v5
du_isCommutativeBand_1262 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_1262 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
         (coe
            MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
            (coe v1)))
-- Data.Sign.Properties._.IsKleeneAlgebra.isCommutativeMagma
d_isCommutativeMagma_1264 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1264 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_1264 v5
du_isCommutativeMagma_1264 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1264 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1266 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_1266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Sign.Properties._.IsKleeneAlgebra.isCommutativeSemigroup
d_isCommutativeSemigroup_1268 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1268 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_1268 v5
du_isCommutativeSemigroup_1268 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1268 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.+-isIdempotentCommutativeMonoid
d_'43''45'isIdempotentCommutativeMonoid_1270 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_'43''45'isIdempotentCommutativeMonoid_1270 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'43''45'isIdempotentCommutativeMonoid_1270 v5
du_'43''45'isIdempotentCommutativeMonoid_1270 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
du_'43''45'isIdempotentCommutativeMonoid_1270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
         (coe v0))
-- Data.Sign.Properties._.IsKleeneAlgebra.isIdempotentMonoid
d_isIdempotentMonoid_1272 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_1272 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isIdempotentMonoid_1272 v5
du_isIdempotentMonoid_1272 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_1272 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
         (coe
            MAlonzo.Code.Algebra.Structures.du_'43''45'isIdempotentCommutativeMonoid_2100
            (coe v1)))
-- Data.Sign.Properties._.IsKleeneAlgebra.isMagma
d_isMagma_1274 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1274 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.isMonoid
d_isMonoid_1276 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1276 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.isSemigroup
d_isSemigroup_1278 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1278 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.isUnitalMagma
d_isUnitalMagma_1280 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1280 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1280 v5
du_isUnitalMagma_1280 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1280 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.distrib
d_distrib_1282 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1282 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
               (coe v0))))
-- Data.Sign.Properties._.IsKleeneAlgebra.distribʳ
d_distrib'691'_1284 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1284 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.distribˡ
d_distrib'737'_1286 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1286 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.isEquivalence
d_isEquivalence_1288 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1288 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_1290 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1998
d_isIdempotentSemiring_1290 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
      (coe v0)
-- Data.Sign.Properties._.IsKleeneAlgebra.isNearSemiring
d_isNearSemiring_1292 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_1292 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isNearSemiring_1292 v5
du_isNearSemiring_1292 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_1292 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.isPartialEquivalence
d_isPartialEquivalence_1294 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1294 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1294 v5
du_isPartialEquivalence_1294 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1294 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.isSemiring
d_isSemiring_1296 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_1296 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
         (coe v0))
-- Data.Sign.Properties._.IsKleeneAlgebra.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1298 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_1298 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
            (coe v0)))
-- Data.Sign.Properties._.IsKleeneAlgebra.isSemiringWithoutOne
d_isSemiringWithoutOne_1300 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_1300 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isSemiringWithoutOne_1300 v5
du_isSemiringWithoutOne_1300 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_1300 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_2012 (coe v1)))
-- Data.Sign.Properties._.IsKleeneAlgebra.refl
d_refl_1302 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1302 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.reflexive
d_reflexive_1304 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1304 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.setoid
d_setoid_1306 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1306 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_1306 v5
du_setoid_1306 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1306 v0
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
-- Data.Sign.Properties._.IsKleeneAlgebra.starDestructive
d_starDestructive_1308 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_1308 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_starDestructive_2144 (coe v0)
-- Data.Sign.Properties._.IsKleeneAlgebra.starDestructiveʳ
d_starDestructive'691'_1310 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starDestructive'691'_1310 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.starDestructiveˡ
d_starDestructive'737'_1312 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starDestructive'737'_1312 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.starExpansive
d_starExpansive_1314 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_1314 v0
  = coe MAlonzo.Code.Algebra.Structures.d_starExpansive_2142 (coe v0)
-- Data.Sign.Properties._.IsKleeneAlgebra.starExpansiveʳ
d_starExpansive'691'_1316 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starExpansive'691'_1316 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.starExpansiveˡ
d_starExpansive'737'_1318 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_starExpansive'737'_1318 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.sym
d_sym_1320 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1320 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.trans
d_trans_1322 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1322 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.zero
d_zero_1324 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1656
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_2012
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2140
            (coe v0)))
-- Data.Sign.Properties._.IsKleeneAlgebra.zeroʳ
d_zero'691'_1326 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1326 = erased
-- Data.Sign.Properties._.IsKleeneAlgebra.zeroˡ
d_zero'737'_1328 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1328 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.//-cong
d_'47''47''45'cong_1332 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1332 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.//-congʳ
d_'47''47''45'cong'691'_1334 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1334 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.//-congˡ
d_'47''47''45'cong'737'_1336 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1336 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.\\-cong
d_'92''92''45'cong_1338 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1338 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.\\-congʳ
d_'92''92''45'cong'691'_1340 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1340 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.\\-congˡ
d_'92''92''45'cong'737'_1342 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1342 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.identity
d_identity_1344 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1344 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))
-- Data.Sign.Properties._.IsLeftBolLoop.identityʳ
d_identity'691'_1346 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1346 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.identityˡ
d_identity'737'_1348 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1348 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.isEquivalence
d_isEquivalence_1350 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1350 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))))
-- Data.Sign.Properties._.IsLeftBolLoop.isLoop
d_isLoop_1352 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1352 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)
-- Data.Sign.Properties._.IsLeftBolLoop.isMagma
d_isMagma_1354 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1354 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Sign.Properties._.IsLeftBolLoop.isPartialEquivalence
d_isPartialEquivalence_1356 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1356 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1356 v4
du_isPartialEquivalence_1356 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1356 v0
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
-- Data.Sign.Properties._.IsLeftBolLoop.isQuasigroup
d_isQuasigroup_1358 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1358 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0))
-- Data.Sign.Properties._.IsLeftBolLoop.leftBol
d_leftBol_1360 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1360 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.leftDivides
d_leftDivides_1362 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1362 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Sign.Properties._.IsLeftBolLoop.leftDividesʳ
d_leftDivides'691'_1364 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1364 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.leftDividesˡ
d_leftDivides'737'_1366 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1366 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.refl
d_refl_1368 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1368 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.reflexive
d_reflexive_1370 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1370 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.rightDivides
d_rightDivides_1372 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1372 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0)))
-- Data.Sign.Properties._.IsLeftBolLoop.rightDividesʳ
d_rightDivides'691'_1374 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1374 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.rightDividesˡ
d_rightDivides'737'_1376 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1376 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.setoid
d_setoid_1378 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1378 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1378 v4
du_setoid_1378 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1378 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3216 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Sign.Properties._.IsLeftBolLoop.sym
d_sym_1380 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1380 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.trans
d_trans_1382 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1382 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.∙-cong
d_'8729''45'cong_1384 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1384 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.∙-congʳ
d_'8729''45'cong'691'_1386 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1386 = erased
-- Data.Sign.Properties._.IsLeftBolLoop.∙-congˡ
d_'8729''45'cong'737'_1388 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1388 = erased
-- Data.Sign.Properties._.IsLoop.//-cong
d_'47''47''45'cong_1392 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1392 = erased
-- Data.Sign.Properties._.IsLoop.//-congʳ
d_'47''47''45'cong'691'_1394 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1394 = erased
-- Data.Sign.Properties._.IsLoop.//-congˡ
d_'47''47''45'cong'737'_1396 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1396 = erased
-- Data.Sign.Properties._.IsLoop.\\-cong
d_'92''92''45'cong_1398 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1398 = erased
-- Data.Sign.Properties._.IsLoop.\\-congʳ
d_'92''92''45'cong'691'_1400 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1400 = erased
-- Data.Sign.Properties._.IsLoop.\\-congˡ
d_'92''92''45'cong'737'_1402 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1402 = erased
-- Data.Sign.Properties._.IsLoop.identity
d_identity_1404 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1404 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_3138 (coe v0)
-- Data.Sign.Properties._.IsLoop.identityʳ
d_identity'691'_1406 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1406 = erased
-- Data.Sign.Properties._.IsLoop.identityˡ
d_identity'737'_1408 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1408 = erased
-- Data.Sign.Properties._.IsLoop.isEquivalence
d_isEquivalence_1410 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1410 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0)))
-- Data.Sign.Properties._.IsLoop.isMagma
d_isMagma_1412 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1412 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Sign.Properties._.IsLoop.isPartialEquivalence
d_isPartialEquivalence_1414 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1414 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1414 v4
du_isPartialEquivalence_1414 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1414 v0
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
-- Data.Sign.Properties._.IsLoop.isQuasigroup
d_isQuasigroup_1416 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1416 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0)
-- Data.Sign.Properties._.IsLoop.leftDivides
d_leftDivides_1418 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1418 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Sign.Properties._.IsLoop.leftDividesʳ
d_leftDivides'691'_1420 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1420 = erased
-- Data.Sign.Properties._.IsLoop.leftDividesˡ
d_leftDivides'737'_1422 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1422 = erased
-- Data.Sign.Properties._.IsLoop.refl
d_refl_1424 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1424 = erased
-- Data.Sign.Properties._.IsLoop.reflexive
d_reflexive_1426 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1426 = erased
-- Data.Sign.Properties._.IsLoop.rightDivides
d_rightDivides_1428 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1428 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0))
-- Data.Sign.Properties._.IsLoop.rightDividesʳ
d_rightDivides'691'_1430 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1430 = erased
-- Data.Sign.Properties._.IsLoop.rightDividesˡ
d_rightDivides'737'_1432 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1432 = erased
-- Data.Sign.Properties._.IsLoop.setoid
d_setoid_1434 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1434 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1434 v4
du_setoid_1434 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1434 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v1)))
-- Data.Sign.Properties._.IsLoop.sym
d_sym_1436 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1436 = erased
-- Data.Sign.Properties._.IsLoop.trans
d_trans_1438 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1438 = erased
-- Data.Sign.Properties._.IsLoop.∙-cong
d_'8729''45'cong_1440 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1440 = erased
-- Data.Sign.Properties._.IsLoop.∙-congʳ
d_'8729''45'cong'691'_1442 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1442 = erased
-- Data.Sign.Properties._.IsLoop.∙-congˡ
d_'8729''45'cong'737'_1444 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1444 = erased
-- Data.Sign.Properties._.IsMagma.isEquivalence
d_isEquivalence_1448 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1448 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0)
-- Data.Sign.Properties._.IsMagma.isPartialEquivalence
d_isPartialEquivalence_1450 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1450 ~v0 v1
  = du_isPartialEquivalence_1450 v1
du_isPartialEquivalence_1450 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1450 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0))
-- Data.Sign.Properties._.IsMagma.refl
d_refl_1452 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1452 = erased
-- Data.Sign.Properties._.IsMagma.reflexive
d_reflexive_1454 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1454 = erased
-- Data.Sign.Properties._.IsMagma.setoid
d_setoid_1456 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1456 v0 v1
  = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 v1
-- Data.Sign.Properties._.IsMagma.sym
d_sym_1458 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1458 = erased
-- Data.Sign.Properties._.IsMagma.trans
d_trans_1460 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1460 = erased
-- Data.Sign.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1462 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1462 = erased
-- Data.Sign.Properties._.IsMagma.∙-congʳ
d_'8729''45'cong'691'_1464 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1464 = erased
-- Data.Sign.Properties._.IsMagma.∙-congˡ
d_'8729''45'cong'737'_1466 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1466 = erased
-- Data.Sign.Properties._.IsMedialMagma.isEquivalence
d_isEquivalence_1470 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1470 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0))
-- Data.Sign.Properties._.IsMedialMagma.isMagma
d_isMagma_1472 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1472 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0)
-- Data.Sign.Properties._.IsMedialMagma.isPartialEquivalence
d_isPartialEquivalence_1474 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1474 ~v0 v1
  = du_isPartialEquivalence_1474 v1
du_isPartialEquivalence_1474 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1474 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsMedialMagma.medial
d_medial_1476 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_medial_1476 = erased
-- Data.Sign.Properties._.IsMedialMagma.refl
d_refl_1478 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1478 = erased
-- Data.Sign.Properties._.IsMedialMagma.reflexive
d_reflexive_1480 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1480 = erased
-- Data.Sign.Properties._.IsMedialMagma.setoid
d_setoid_1482 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1482 ~v0 v1 = du_setoid_1482 v1
du_setoid_1482 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1482 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_378 (coe v0))
-- Data.Sign.Properties._.IsMedialMagma.sym
d_sym_1484 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1484 = erased
-- Data.Sign.Properties._.IsMedialMagma.trans
d_trans_1486 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1486 = erased
-- Data.Sign.Properties._.IsMedialMagma.∙-cong
d_'8729''45'cong_1488 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1488 = erased
-- Data.Sign.Properties._.IsMedialMagma.∙-congʳ
d_'8729''45'cong'691'_1490 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1490 = erased
-- Data.Sign.Properties._.IsMedialMagma.∙-congˡ
d_'8729''45'cong'737'_1492 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1492 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.//-cong
d_'47''47''45'cong_1496 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1496 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.//-congʳ
d_'47''47''45'cong'691'_1498 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1498 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.//-congˡ
d_'47''47''45'cong'737'_1500 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1500 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.\\-cong
d_'92''92''45'cong_1502 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1502 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.\\-congʳ
d_'92''92''45'cong'691'_1504 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1504 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.\\-congˡ
d_'92''92''45'cong'737'_1506 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1506 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.identity
d_identity_1508 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1508 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))
-- Data.Sign.Properties._.IsMiddleBolLoop.identityʳ
d_identity'691'_1510 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1510 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.identityˡ
d_identity'737'_1512 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1512 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.isEquivalence
d_isEquivalence_1514 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1514 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))))
-- Data.Sign.Properties._.IsMiddleBolLoop.isLoop
d_isLoop_1516 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1516 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)
-- Data.Sign.Properties._.IsMiddleBolLoop.isMagma
d_isMagma_1518 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1518 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Sign.Properties._.IsMiddleBolLoop.isPartialEquivalence
d_isPartialEquivalence_1520 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1520 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1520 v4
du_isPartialEquivalence_1520 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1520 v0
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
-- Data.Sign.Properties._.IsMiddleBolLoop.isQuasigroup
d_isQuasigroup_1522 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1522 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0))
-- Data.Sign.Properties._.IsMiddleBolLoop.leftDivides
d_leftDivides_1524 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1524 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Sign.Properties._.IsMiddleBolLoop.leftDividesʳ
d_leftDivides'691'_1526 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1526 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.leftDividesˡ
d_leftDivides'737'_1528 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1528 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.middleBol
d_middleBol_1530 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_middleBol_1530 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.refl
d_refl_1532 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1532 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.reflexive
d_reflexive_1534 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1534 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.rightDivides
d_rightDivides_1536 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1536 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0)))
-- Data.Sign.Properties._.IsMiddleBolLoop.rightDividesʳ
d_rightDivides'691'_1538 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1538 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.rightDividesˡ
d_rightDivides'737'_1540 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1540 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.setoid
d_setoid_1542 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1542 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1542 v4
du_setoid_1542 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1542 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3476 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Sign.Properties._.IsMiddleBolLoop.sym
d_sym_1544 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1544 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.trans
d_trans_1546 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1546 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.∙-cong
d_'8729''45'cong_1548 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1548 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.∙-congʳ
d_'8729''45'cong'691'_1550 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1550 = erased
-- Data.Sign.Properties._.IsMiddleBolLoop.∙-congˡ
d_'8729''45'cong'737'_1552 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3462 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1552 = erased
-- Data.Sign.Properties._.IsMonoid.assoc
d_assoc_1556 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1556 = erased
-- Data.Sign.Properties._.IsMonoid.identity
d_identity_1558 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1558 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_724 (coe v0)
-- Data.Sign.Properties._.IsMonoid.identityʳ
d_identity'691'_1560 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1560 = erased
-- Data.Sign.Properties._.IsMonoid.identityˡ
d_identity'737'_1562 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1562 = erased
-- Data.Sign.Properties._.IsMonoid.isEquivalence
d_isEquivalence_1564 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1564 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)))
-- Data.Sign.Properties._.IsMonoid.isMagma
d_isMagma_1566 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1566 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0))
-- Data.Sign.Properties._.IsMonoid.isPartialEquivalence
d_isPartialEquivalence_1568 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1568 ~v0 ~v1 v2
  = du_isPartialEquivalence_1568 v2
du_isPartialEquivalence_1568 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1568 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v2))))
-- Data.Sign.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1570 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1570 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)
-- Data.Sign.Properties._.IsMonoid.isUnitalMagma
d_isUnitalMagma_1572 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1572 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756 v2
-- Data.Sign.Properties._.IsMonoid.refl
d_refl_1574 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1574 = erased
-- Data.Sign.Properties._.IsMonoid.reflexive
d_reflexive_1576 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1576 = erased
-- Data.Sign.Properties._.IsMonoid.setoid
d_setoid_1578 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1578 ~v0 ~v1 v2 = du_setoid_1578 v2
du_setoid_1578 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1578 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_setoid_202
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v1)))
-- Data.Sign.Properties._.IsMonoid.sym
d_sym_1580 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1580 = erased
-- Data.Sign.Properties._.IsMonoid.trans
d_trans_1582 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1582 = erased
-- Data.Sign.Properties._.IsMonoid.∙-cong
d_'8729''45'cong_1584 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1584 = erased
-- Data.Sign.Properties._.IsMonoid.∙-congʳ
d_'8729''45'cong'691'_1586 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1586 = erased
-- Data.Sign.Properties._.IsMonoid.∙-congˡ
d_'8729''45'cong'737'_1588 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1588 = erased
-- Data.Sign.Properties._.IsMoufangLoop.//-cong
d_'47''47''45'cong_1592 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1592 = erased
-- Data.Sign.Properties._.IsMoufangLoop.//-congʳ
d_'47''47''45'cong'691'_1594 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1594 = erased
-- Data.Sign.Properties._.IsMoufangLoop.//-congˡ
d_'47''47''45'cong'737'_1596 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1596 = erased
-- Data.Sign.Properties._.IsMoufangLoop.\\-cong
d_'92''92''45'cong_1598 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1598 = erased
-- Data.Sign.Properties._.IsMoufangLoop.\\-congʳ
d_'92''92''45'cong'691'_1600 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1600 = erased
-- Data.Sign.Properties._.IsMoufangLoop.\\-congˡ
d_'92''92''45'cong'737'_1602 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1602 = erased
-- Data.Sign.Properties._.IsMoufangLoop.identical
d_identical_1604 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identical_1604 = erased
-- Data.Sign.Properties._.IsMoufangLoop.identity
d_identity_1606 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1606 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3216
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)))
-- Data.Sign.Properties._.IsMoufangLoop.identityʳ
d_identity'691'_1608 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1608 = erased
-- Data.Sign.Properties._.IsMoufangLoop.identityˡ
d_identity'737'_1610 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1610 = erased
-- Data.Sign.Properties._.IsMoufangLoop.isEquivalence
d_isEquivalence_1612 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1612 v0
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
-- Data.Sign.Properties._.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_1614 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3202
d_isLeftBolLoop_1614 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)
-- Data.Sign.Properties._.IsMoufangLoop.isLoop
d_isLoop_1616 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_1616 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isLoop_3216
      (coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))
-- Data.Sign.Properties._.IsMoufangLoop.isMagma
d_isMagma_1618 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1618 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Sign.Properties._.IsMoufangLoop.isPartialEquivalence
d_isPartialEquivalence_1620 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1620 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1620 v4
du_isPartialEquivalence_1620 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1620 v0
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
-- Data.Sign.Properties._.IsMoufangLoop.isQuasigroup
d_isQuasigroup_1622 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_1622 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3216
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0)))
-- Data.Sign.Properties._.IsMoufangLoop.leftBol
d_leftBol_1624 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1624 = erased
-- Data.Sign.Properties._.IsMoufangLoop.leftDivides
d_leftDivides_1626 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1626 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Sign.Properties._.IsMoufangLoop.leftDividesʳ
d_leftDivides'691'_1628 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1628 = erased
-- Data.Sign.Properties._.IsMoufangLoop.leftDividesˡ
d_leftDivides'737'_1630 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1630 = erased
-- Data.Sign.Properties._.IsMoufangLoop.refl
d_refl_1632 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1632 = erased
-- Data.Sign.Properties._.IsMoufangLoop.reflexive
d_reflexive_1634 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1634 = erased
-- Data.Sign.Properties._.IsMoufangLoop.rightBol
d_rightBol_1636 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_1636 = erased
-- Data.Sign.Properties._.IsMoufangLoop.rightDivides
d_rightDivides_1638 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1638 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3216
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3386 (coe v0))))
-- Data.Sign.Properties._.IsMoufangLoop.rightDividesʳ
d_rightDivides'691'_1640 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1640 = erased
-- Data.Sign.Properties._.IsMoufangLoop.rightDividesˡ
d_rightDivides'737'_1642 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1642 = erased
-- Data.Sign.Properties._.IsMoufangLoop.setoid
d_setoid_1644 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1644 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_1644 v4
du_setoid_1644 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1644 v0
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
-- Data.Sign.Properties._.IsMoufangLoop.sym
d_sym_1646 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1646 = erased
-- Data.Sign.Properties._.IsMoufangLoop.trans
d_trans_1648 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1648 = erased
-- Data.Sign.Properties._.IsMoufangLoop.∙-cong
d_'8729''45'cong_1650 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1650 = erased
-- Data.Sign.Properties._.IsMoufangLoop.∙-congʳ
d_'8729''45'cong'691'_1652 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1652 = erased
-- Data.Sign.Properties._.IsMoufangLoop.∙-congˡ
d_'8729''45'cong'737'_1654 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3370 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1654 = erased
-- Data.Sign.Properties._.IsNearSemiring.*-assoc
d_'42''45'assoc_1658 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1658 = erased
-- Data.Sign.Properties._.IsNearSemiring.*-cong
d_'42''45'cong_1660 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1660 = erased
-- Data.Sign.Properties._.IsNearSemiring.∙-congʳ
d_'8729''45'cong'691'_1662 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1662 = erased
-- Data.Sign.Properties._.IsNearSemiring.∙-congˡ
d_'8729''45'cong'737'_1664 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1664 = erased
-- Data.Sign.Properties._.IsNearSemiring.*-isMagma
d_'42''45'isMagma_1666 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1666 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324 v3
-- Data.Sign.Properties._.IsNearSemiring.*-isSemigroup
d_'42''45'isSemigroup_1668 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1668 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326 v3
-- Data.Sign.Properties._.IsNearSemiring.assoc
d_assoc_1670 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1670 = erased
-- Data.Sign.Properties._.IsNearSemiring.∙-cong
d_'8729''45'cong_1672 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1672 = erased
-- Data.Sign.Properties._.IsNearSemiring.∙-congʳ
d_'8729''45'cong'691'_1674 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1674 = erased
-- Data.Sign.Properties._.IsNearSemiring.∙-congˡ
d_'8729''45'cong'737'_1676 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1676 = erased
-- Data.Sign.Properties._.IsNearSemiring.identity
d_identity_1678 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1678 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Sign.Properties._.IsNearSemiring.identityʳ
d_identity'691'_1680 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1680 = erased
-- Data.Sign.Properties._.IsNearSemiring.identityˡ
d_identity'737'_1682 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1682 = erased
-- Data.Sign.Properties._.IsNearSemiring.isMagma
d_isMagma_1684 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1684 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0)))
-- Data.Sign.Properties._.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1686 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1686 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0)
-- Data.Sign.Properties._.IsNearSemiring.isSemigroup
d_isSemigroup_1688 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1688 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Sign.Properties._.IsNearSemiring.isUnitalMagma
d_isUnitalMagma_1690 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1690 ~v0 ~v1 ~v2 v3 = du_isUnitalMagma_1690 v3
du_isUnitalMagma_1690 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1690 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))
-- Data.Sign.Properties._.IsNearSemiring.distribʳ
d_distrib'691'_1692 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1692 = erased
-- Data.Sign.Properties._.IsNearSemiring.isEquivalence
d_isEquivalence_1694 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1694 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1278 (coe v0))))
-- Data.Sign.Properties._.IsNearSemiring.isPartialEquivalence
d_isPartialEquivalence_1696 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1696 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1696 v3
du_isPartialEquivalence_1696 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1696 v0
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
-- Data.Sign.Properties._.IsNearSemiring.refl
d_refl_1698 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1698 = erased
-- Data.Sign.Properties._.IsNearSemiring.reflexive
d_reflexive_1700 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1700 = erased
-- Data.Sign.Properties._.IsNearSemiring.setoid
d_setoid_1702 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1702 ~v0 ~v1 ~v2 v3 = du_setoid_1702 v3
du_setoid_1702 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1702 v0
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
-- Data.Sign.Properties._.IsNearSemiring.sym
d_sym_1704 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1704 = erased
-- Data.Sign.Properties._.IsNearSemiring.trans
d_trans_1706 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1706 = erased
-- Data.Sign.Properties._.IsNearSemiring.zeroˡ
d_zero'737'_1708 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1708 = erased
-- Data.Sign.Properties._.IsNearring.*-assoc
d_'42''45'assoc_1712 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1712 = erased
-- Data.Sign.Properties._.IsNearring.*-cong
d_'42''45'cong_1714 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1714 = erased
-- Data.Sign.Properties._.IsNearring.∙-congʳ
d_'8729''45'cong'691'_1716 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1716 = erased
-- Data.Sign.Properties._.IsNearring.∙-congˡ
d_'8729''45'cong'737'_1718 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1718 = erased
-- Data.Sign.Properties._.IsNearring.*-identity
d_'42''45'identity_1720 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1720 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2288
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Sign.Properties._.IsNearring.identityʳ
d_identity'691'_1722 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1722 = erased
-- Data.Sign.Properties._.IsNearring.identityˡ
d_identity'737'_1724 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1724 = erased
-- Data.Sign.Properties._.IsNearring.*-isMagma
d_'42''45'isMagma_1726 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1726 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMagma_1726 v5
du_'42''45'isMagma_1726 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_1726 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2342
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Sign.Properties._.IsNearring.*-isMonoid
d_'42''45'isMonoid_1728 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1728 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isMonoid_1728 v5
du_'42''45'isMonoid_1728 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_1728 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2346
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Sign.Properties._.IsNearring.*-isSemigroup
d_'42''45'isSemigroup_1730 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1730 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'42''45'isSemigroup_1730 v5
du_'42''45'isSemigroup_1730 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_1730 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_2344
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Sign.Properties._.IsNearring.assoc
d_assoc_1732 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1732 = erased
-- Data.Sign.Properties._.IsNearring.∙-cong
d_'8729''45'cong_1734 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1734 = erased
-- Data.Sign.Properties._.IsNearring.∙-congʳ
d_'8729''45'cong'691'_1736 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1736 = erased
-- Data.Sign.Properties._.IsNearring.∙-congˡ
d_'8729''45'cong'737'_1738 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1738 = erased
-- Data.Sign.Properties._.IsNearring.identity
d_identity_1740 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1740 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))
-- Data.Sign.Properties._.IsNearring.identityʳ
d_identity'691'_1742 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1742 = erased
-- Data.Sign.Properties._.IsNearring.identityˡ
d_identity'737'_1744 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1744 = erased
-- Data.Sign.Properties._.IsNearring.+-inverse
d_'43''45'inverse_1746 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_1746 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'inverse_2646 (coe v0)
-- Data.Sign.Properties._.IsNearring.+-inverseʳ
d_'43''45'inverse'691'_1748 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'691'_1748 = erased
-- Data.Sign.Properties._.IsNearring.+-inverseˡ
d_'43''45'inverse'737'_1750 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'inverse'737'_1750 = erased
-- Data.Sign.Properties._.IsNearring.isMagma
d_isMagma_1752 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1752 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
            (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))))
-- Data.Sign.Properties._.IsNearring.+-isMonoid
d_'43''45'isMonoid_1754 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1754 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Sign.Properties._.IsNearring.isSemigroup
d_isSemigroup_1756 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1756 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)))
-- Data.Sign.Properties._.IsNearring.isUnitalMagma
d_isUnitalMagma_1758 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1758 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1758 v5
du_isUnitalMagma_1758 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1758 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v1)))
-- Data.Sign.Properties._.IsNearring.distrib
d_distrib_1760 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1760 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2290
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Sign.Properties._.IsNearring.distribʳ
d_distrib'691'_1762 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1762 = erased
-- Data.Sign.Properties._.IsNearring.distribˡ
d_distrib'737'_1764 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1764 = erased
-- Data.Sign.Properties._.IsNearring.identityʳ
d_identity'691'_1766 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1766 = erased
-- Data.Sign.Properties._.IsNearring.identityˡ
d_identity'737'_1768 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1768 = erased
-- Data.Sign.Properties._.IsNearring.isEquivalence
d_isEquivalence_1770 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1770 v0
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
-- Data.Sign.Properties._.IsNearring.isPartialEquivalence
d_isPartialEquivalence_1772 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1772 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1772 v5
du_isPartialEquivalence_1772 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1772 v0
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
-- Data.Sign.Properties._.IsNearring.isQuasiring
d_isQuasiring_1774 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260
d_isQuasiring_1774 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0)
-- Data.Sign.Properties._.IsNearring.refl
d_refl_1776 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1776 = erased
-- Data.Sign.Properties._.IsNearring.reflexive
d_reflexive_1778 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1778 = erased
-- Data.Sign.Properties._.IsNearring.setoid
d_setoid_1780 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1780 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_1780 v5
du_setoid_1780 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1780 v0
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
-- Data.Sign.Properties._.IsNearring.sym
d_sym_1782 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1782 = erased
-- Data.Sign.Properties._.IsNearring.trans
d_trans_1784 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1784 = erased
-- Data.Sign.Properties._.IsNearring.zero
d_zero_1786 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1786 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_2292
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2644 (coe v0))
-- Data.Sign.Properties._.IsNearring.zeroʳ
d_zero'691'_1788 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1788 = erased
-- Data.Sign.Properties._.IsNearring.zeroˡ
d_zero'737'_1790 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1790 = erased
-- Data.Sign.Properties._.IsNearring.⁻¹-cong
d_'8315''185''45'cong_1792 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2626 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1792 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing._//_
d__'47''47'__1796 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
d__'47''47'__1796 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__1796 v0 v2
du__'47''47'__1796 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
du__'47''47'__1796 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Sign.Properties._.IsNonAssociativeRing.*-cong
d_'42''45'cong_1798 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1798 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.∙-congʳ
d_'8729''45'cong'691'_1800 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1800 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.∙-congˡ
d_'8729''45'cong'737'_1802 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1802 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.*-identity
d_'42''45'identity_1804 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1804 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2520 (coe v0)
-- Data.Sign.Properties._.IsNonAssociativeRing.*-identityʳ
d_'42''45'identity'691'_1806 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_1806 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.*-identityˡ
d_'42''45'identity'737'_1808 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_1808 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.*-isMagma
d_'42''45'isMagma_1810 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1810 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2600 v5
-- Data.Sign.Properties._.IsNonAssociativeRing.*-isUnitalMagma
d_'42''45'isUnitalMagma_1812 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_'42''45'isUnitalMagma_1812 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isUnitalMagma_2606 v5
-- Data.Sign.Properties._.IsNonAssociativeRing.assoc
d_assoc_1814 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1814 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.comm
d_comm_1816 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1816 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.∙-cong
d_'8729''45'cong_1818 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1818 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.∙-congʳ
d_'8729''45'cong'691'_1820 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1820 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.∙-congˡ
d_'8729''45'cong'737'_1822 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1822 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.identity
d_identity_1824 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1824 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
               (coe v0))))
-- Data.Sign.Properties._.IsNonAssociativeRing.identityʳ
d_identity'691'_1826 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1826 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.identityˡ
d_identity'737'_1828 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1828 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_1830 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_1830 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
      (coe v0)
-- Data.Sign.Properties._.IsNonAssociativeRing.isCommutativeMagma
d_isCommutativeMagma_1832 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_1832 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_1832 v5
du_isCommutativeMagma_1832 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_1832 v0
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
-- Data.Sign.Properties._.IsNonAssociativeRing.isCommutativeMonoid
d_isCommutativeMonoid_1834 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_1834 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_1834 v5
du_isCommutativeMonoid_1834 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_1834 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
         (coe v0))
-- Data.Sign.Properties._.IsNonAssociativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_1836 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_1836 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_1836 v5
du_isCommutativeSemigroup_1836 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_1836 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
            (coe v1)))
-- Data.Sign.Properties._.IsNonAssociativeRing.isGroup
d_isGroup_1838 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_1838 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
         (coe v0))
-- Data.Sign.Properties._.IsNonAssociativeRing.isInvertibleMagma
d_isInvertibleMagma_1840 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_1840 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_1840 v5
du_isInvertibleMagma_1840 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_1840 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Sign.Properties._.IsNonAssociativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_1842 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_1842 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_1842 v5
du_isInvertibleUnitalMagma_1842 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_1842 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Sign.Properties._.IsNonAssociativeRing.isMagma
d_isMagma_1844 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1844 v0
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
-- Data.Sign.Properties._.IsNonAssociativeRing.isMonoid
d_isMonoid_1846 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_1846 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
            (coe v0)))
-- Data.Sign.Properties._.IsNonAssociativeRing.isSemigroup
d_isSemigroup_1848 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1848 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
               (coe v0))))
-- Data.Sign.Properties._.IsNonAssociativeRing.isUnitalMagma
d_isUnitalMagma_1850 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1850 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_1850 v5
du_isUnitalMagma_1850 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1850 v0
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
-- Data.Sign.Properties._.IsNonAssociativeRing.⁻¹-cong
d_'8315''185''45'cong_1852 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1852 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.inverse
d_inverse_1854 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1854 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2516
            (coe v0)))
-- Data.Sign.Properties._.IsNonAssociativeRing.inverseʳ
d_inverse'691'_1856 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_1856 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.inverseˡ
d_inverse'737'_1858 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_1858 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.distrib
d_distrib_1860 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1860 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2522 (coe v0)
-- Data.Sign.Properties._.IsNonAssociativeRing.distribʳ
d_distrib'691'_1862 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1862 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.distribˡ
d_distrib'737'_1864 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1864 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.isEquivalence
d_isEquivalence_1866 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1866 v0
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
-- Data.Sign.Properties._.IsNonAssociativeRing.isPartialEquivalence
d_isPartialEquivalence_1868 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1868 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_1868 v5
du_isPartialEquivalence_1868 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1868 v0
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
-- Data.Sign.Properties._.IsNonAssociativeRing.refl
d_refl_1870 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1870 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.reflexive
d_reflexive_1872 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1872 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.setoid
d_setoid_1874 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1874 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_1874 v5
du_setoid_1874 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1874 v0
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
-- Data.Sign.Properties._.IsNonAssociativeRing.sym
d_sym_1876 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1876 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.trans
d_trans_1878 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1878 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_1880 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_1880 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_1882 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_1882 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.zero
d_zero_1884 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1884 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2524 (coe v0)
-- Data.Sign.Properties._.IsNonAssociativeRing.zeroʳ
d_zero'691'_1886 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_1886 = erased
-- Data.Sign.Properties._.IsNonAssociativeRing.zeroˡ
d_zero'737'_1888 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2494 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1888 = erased
-- Data.Sign.Properties._.IsQuasigroup.//-cong
d_'47''47''45'cong_1892 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1892 = erased
-- Data.Sign.Properties._.IsQuasigroup.//-congʳ
d_'47''47''45'cong'691'_1894 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_1894 = erased
-- Data.Sign.Properties._.IsQuasigroup.//-congˡ
d_'47''47''45'cong'737'_1896 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_1896 = erased
-- Data.Sign.Properties._.IsQuasigroup.\\-cong
d_'92''92''45'cong_1898 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1898 = erased
-- Data.Sign.Properties._.IsQuasigroup.\\-congʳ
d_'92''92''45'cong'691'_1900 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_1900 = erased
-- Data.Sign.Properties._.IsQuasigroup.\\-congˡ
d_'92''92''45'cong'737'_1902 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_1902 = erased
-- Data.Sign.Properties._.IsQuasigroup.isEquivalence
d_isEquivalence_1904 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1904 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0))
-- Data.Sign.Properties._.IsQuasigroup.isMagma
d_isMagma_1906 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1906 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0)
-- Data.Sign.Properties._.IsQuasigroup.isPartialEquivalence
d_isPartialEquivalence_1908 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1908 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1908 v3
du_isPartialEquivalence_1908 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1908 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsQuasigroup.leftDivides
d_leftDivides_1910 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1910 v0
  = coe MAlonzo.Code.Algebra.Structures.d_leftDivides_3062 (coe v0)
-- Data.Sign.Properties._.IsQuasigroup.leftDividesʳ
d_leftDivides'691'_1912 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_1912 = erased
-- Data.Sign.Properties._.IsQuasigroup.leftDividesˡ
d_leftDivides'737'_1914 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_1914 = erased
-- Data.Sign.Properties._.IsQuasigroup.refl
d_refl_1916 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1916 = erased
-- Data.Sign.Properties._.IsQuasigroup.reflexive
d_reflexive_1918 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1918 = erased
-- Data.Sign.Properties._.IsQuasigroup.rightDivides
d_rightDivides_1920 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1920 v0
  = coe MAlonzo.Code.Algebra.Structures.d_rightDivides_3064 (coe v0)
-- Data.Sign.Properties._.IsQuasigroup.rightDividesʳ
d_rightDivides'691'_1922 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_1922 = erased
-- Data.Sign.Properties._.IsQuasigroup.rightDividesˡ
d_rightDivides'737'_1924 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_1924 = erased
-- Data.Sign.Properties._.IsQuasigroup.setoid
d_setoid_1926 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1926 ~v0 ~v1 ~v2 v3 = du_setoid_1926 v3
du_setoid_1926 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1926 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v0))
-- Data.Sign.Properties._.IsQuasigroup.sym
d_sym_1928 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_1928 = erased
-- Data.Sign.Properties._.IsQuasigroup.trans
d_trans_1930 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_1930 = erased
-- Data.Sign.Properties._.IsQuasigroup.∙-cong
d_'8729''45'cong_1932 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1932 = erased
-- Data.Sign.Properties._.IsQuasigroup.∙-congʳ
d_'8729''45'cong'691'_1934 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1934 = erased
-- Data.Sign.Properties._.IsQuasigroup.∙-congˡ
d_'8729''45'cong'737'_1936 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1936 = erased
-- Data.Sign.Properties._.IsQuasiring.*-assoc
d_'42''45'assoc_1940 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1940 = erased
-- Data.Sign.Properties._.IsQuasiring.*-cong
d_'42''45'cong_1942 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1942 = erased
-- Data.Sign.Properties._.IsQuasiring.∙-congʳ
d_'8729''45'cong'691'_1944 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1944 = erased
-- Data.Sign.Properties._.IsQuasiring.∙-congˡ
d_'8729''45'cong'737'_1946 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1946 = erased
-- Data.Sign.Properties._.IsQuasiring.*-identity
d_'42''45'identity_1948 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1948 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2288 (coe v0)
-- Data.Sign.Properties._.IsQuasiring.identityʳ
d_identity'691'_1950 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1950 = erased
-- Data.Sign.Properties._.IsQuasiring.identityˡ
d_identity'737'_1952 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1952 = erased
-- Data.Sign.Properties._.IsQuasiring.*-isMagma
d_'42''45'isMagma_1954 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_1954 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_2342 v4
-- Data.Sign.Properties._.IsQuasiring.*-isMonoid
d_'42''45'isMonoid_1956 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_1956 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2346 v4
-- Data.Sign.Properties._.IsQuasiring.*-isSemigroup
d_'42''45'isSemigroup_1958 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_1958 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_2344 v4
-- Data.Sign.Properties._.IsQuasiring.assoc
d_assoc_1960 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1960 = erased
-- Data.Sign.Properties._.IsQuasiring.∙-cong
d_'8729''45'cong_1962 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1962 = erased
-- Data.Sign.Properties._.IsQuasiring.∙-congʳ
d_'8729''45'cong'691'_1964 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_1964 = erased
-- Data.Sign.Properties._.IsQuasiring.∙-congˡ
d_'8729''45'cong'737'_1966 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_1966 = erased
-- Data.Sign.Properties._.IsQuasiring.identity
d_identity_1968 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1968 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Sign.Properties._.IsQuasiring.identityʳ
d_identity'691'_1970 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1970 = erased
-- Data.Sign.Properties._.IsQuasiring.identityˡ
d_identity'737'_1972 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1972 = erased
-- Data.Sign.Properties._.IsQuasiring.isMagma
d_isMagma_1974 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_1974 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0)))
-- Data.Sign.Properties._.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_1976 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''45'isMonoid_1976 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0)
-- Data.Sign.Properties._.IsQuasiring.isSemigroup
d_isSemigroup_1978 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1978 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Sign.Properties._.IsQuasiring.isUnitalMagma
d_isUnitalMagma_1980 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_1980 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_1980 v4
du_isUnitalMagma_1980 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_1980 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))
-- Data.Sign.Properties._.IsQuasiring.distrib
d_distrib_1982 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1982 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2290 (coe v0)
-- Data.Sign.Properties._.IsQuasiring.distribʳ
d_distrib'691'_1984 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1984 = erased
-- Data.Sign.Properties._.IsQuasiring.distribˡ
d_distrib'737'_1986 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_1986 = erased
-- Data.Sign.Properties._.IsQuasiring.identityʳ
d_identity'691'_1988 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_1988 = erased
-- Data.Sign.Properties._.IsQuasiring.identityˡ
d_identity'737'_1990 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_1990 = erased
-- Data.Sign.Properties._.IsQuasiring.isEquivalence
d_isEquivalence_1992 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1992 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2282 (coe v0))))
-- Data.Sign.Properties._.IsQuasiring.isPartialEquivalence
d_isPartialEquivalence_1994 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1994 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_1994 v4
du_isPartialEquivalence_1994 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1994 v0
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
-- Data.Sign.Properties._.IsQuasiring.refl
d_refl_1996 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_1996 = erased
-- Data.Sign.Properties._.IsQuasiring.reflexive
d_reflexive_1998 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_1998 = erased
-- Data.Sign.Properties._.IsQuasiring.setoid
d_setoid_2000 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2000 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2000 v4
du_setoid_2000 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2000 v0
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
-- Data.Sign.Properties._.IsQuasiring.sym
d_sym_2002 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2002 = erased
-- Data.Sign.Properties._.IsQuasiring.trans
d_trans_2004 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2004 = erased
-- Data.Sign.Properties._.IsQuasiring.zero
d_zero_2006 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2006 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2292 (coe v0)
-- Data.Sign.Properties._.IsQuasiring.zeroʳ
d_zero'691'_2008 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2008 = erased
-- Data.Sign.Properties._.IsQuasiring.zeroˡ
d_zero'737'_2010 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2260 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2010 = erased
-- Data.Sign.Properties._.IsRightBolLoop.//-cong
d_'47''47''45'cong_2014 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2014 = erased
-- Data.Sign.Properties._.IsRightBolLoop.//-congʳ
d_'47''47''45'cong'691'_2016 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'691'_2016 = erased
-- Data.Sign.Properties._.IsRightBolLoop.//-congˡ
d_'47''47''45'cong'737'_2018 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong'737'_2018 = erased
-- Data.Sign.Properties._.IsRightBolLoop.\\-cong
d_'92''92''45'cong_2020 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2020 = erased
-- Data.Sign.Properties._.IsRightBolLoop.\\-congʳ
d_'92''92''45'cong'691'_2022 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'691'_2022 = erased
-- Data.Sign.Properties._.IsRightBolLoop.\\-congˡ
d_'92''92''45'cong'737'_2024 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong'737'_2024 = erased
-- Data.Sign.Properties._.IsRightBolLoop.identity
d_identity_2026 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2026 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3138
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))
-- Data.Sign.Properties._.IsRightBolLoop.identityʳ
d_identity'691'_2028 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2028 = erased
-- Data.Sign.Properties._.IsRightBolLoop.identityˡ
d_identity'737'_2030 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2030 = erased
-- Data.Sign.Properties._.IsRightBolLoop.isEquivalence
d_isEquivalence_2032 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2032 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_3056
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))))
-- Data.Sign.Properties._.IsRightBolLoop.isLoop
d_isLoop_2034 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3122
d_isLoop_2034 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)
-- Data.Sign.Properties._.IsRightBolLoop.isMagma
d_isMagma_2036 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2036 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_3056
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Sign.Properties._.IsRightBolLoop.isPartialEquivalence
d_isPartialEquivalence_2038 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2038 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2038 v4
du_isPartialEquivalence_2038 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2038 v0
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
-- Data.Sign.Properties._.IsRightBolLoop.isQuasigroup
d_isQuasigroup_2040 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_3038
d_isQuasigroup_2040 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0))
-- Data.Sign.Properties._.IsRightBolLoop.leftDivides
d_leftDivides_2042 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2042 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_3062
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Sign.Properties._.IsRightBolLoop.leftDividesʳ
d_leftDivides'691'_2044 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'691'_2044 = erased
-- Data.Sign.Properties._.IsRightBolLoop.leftDividesˡ
d_leftDivides'737'_2046 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftDivides'737'_2046 = erased
-- Data.Sign.Properties._.IsRightBolLoop.refl
d_refl_2048 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2048 = erased
-- Data.Sign.Properties._.IsRightBolLoop.reflexive
d_reflexive_2050 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2050 = erased
-- Data.Sign.Properties._.IsRightBolLoop.rightBol
d_rightBol_2052 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_2052 = erased
-- Data.Sign.Properties._.IsRightBolLoop.rightDivides
d_rightDivides_2054 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2054 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_3064
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0)))
-- Data.Sign.Properties._.IsRightBolLoop.rightDividesʳ
d_rightDivides'691'_2056 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'691'_2056 = erased
-- Data.Sign.Properties._.IsRightBolLoop.rightDividesˡ
d_rightDivides'737'_2058 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightDivides'737'_2058 = erased
-- Data.Sign.Properties._.IsRightBolLoop.setoid
d_setoid_2060 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2060 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2060 v4
du_setoid_2060 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2060 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isLoop_3300 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3136 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_202
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_3056 (coe v2))))
-- Data.Sign.Properties._.IsRightBolLoop.sym
d_sym_2062 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2062 = erased
-- Data.Sign.Properties._.IsRightBolLoop.trans
d_trans_2064 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2064 = erased
-- Data.Sign.Properties._.IsRightBolLoop.∙-cong
d_'8729''45'cong_2066 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2066 = erased
-- Data.Sign.Properties._.IsRightBolLoop.∙-congʳ
d_'8729''45'cong'691'_2068 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2068 = erased
-- Data.Sign.Properties._.IsRightBolLoop.∙-congˡ
d_'8729''45'cong'737'_2070 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3286 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2070 = erased
-- Data.Sign.Properties._.IsRing._//_
d__'47''47'__2074 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
d__'47''47'__2074 v0 ~v1 v2 ~v3 ~v4 ~v5 = du__'47''47'__2074 v0 v2
du__'47''47'__2074 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
du__'47''47'__2074 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Sign.Properties._.IsRing.*-assoc
d_'42''45'assoc_2076 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2076 = erased
-- Data.Sign.Properties._.IsRing.*-cong
d_'42''45'cong_2078 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2078 = erased
-- Data.Sign.Properties._.IsRing.∙-congʳ
d_'8729''45'cong'691'_2080 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2080 = erased
-- Data.Sign.Properties._.IsRing.∙-congˡ
d_'8729''45'cong'737'_2082 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2082 = erased
-- Data.Sign.Properties._.IsRing.*-identity
d_'42''45'identity_2084 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2084 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2768 (coe v0)
-- Data.Sign.Properties._.IsRing.identityʳ
d_identity'691'_2086 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2086 = erased
-- Data.Sign.Properties._.IsRing.identityˡ
d_identity'737'_2088 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2088 = erased
-- Data.Sign.Properties._.IsRing.*-isMagma
d_'42''45'isMagma_2090 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2090 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isMagma_2090 v0 v1 v2 v3 v5
du_'42''45'isMagma_2090 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_2090 v0 v1 v2 v3 v4
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
-- Data.Sign.Properties._.IsRing.*-isMonoid
d_'42''45'isMonoid_2092 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2092 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2860 v0 v1 v2
      v3 v5
-- Data.Sign.Properties._.IsRing.*-isSemigroup
d_'42''45'isSemigroup_2094 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2094 v0 v1 v2 v3 ~v4 v5
  = du_'42''45'isSemigroup_2094 v0 v1 v2 v3 v5
du_'42''45'isSemigroup_2094 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_2094 v0 v1 v2 v3 v4
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
-- Data.Sign.Properties._.IsRing.assoc
d_assoc_2096 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2096 = erased
-- Data.Sign.Properties._.IsRing.comm
d_comm_2098 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2098 = erased
-- Data.Sign.Properties._.IsRing.∙-cong
d_'8729''45'cong_2100 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2100 = erased
-- Data.Sign.Properties._.IsRing.∙-congʳ
d_'8729''45'cong'691'_2102 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2102 = erased
-- Data.Sign.Properties._.IsRing.∙-congˡ
d_'8729''45'cong'737'_2104 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2104 = erased
-- Data.Sign.Properties._.IsRing.identity
d_identity_2106 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2106 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_2106 v5
du_identity_2106 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2106 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
               (coe v0))))
-- Data.Sign.Properties._.IsRing.identityʳ
d_identity'691'_2108 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2108 = erased
-- Data.Sign.Properties._.IsRing.identityˡ
d_identity'737'_2110 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2110 = erased
-- Data.Sign.Properties._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2112 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2112 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
      (coe v0)
-- Data.Sign.Properties._.IsRing.isCommutativeMagma
d_isCommutativeMagma_2114 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2114 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMagma_2114 v5
du_isCommutativeMagma_2114 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2114 v0
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
-- Data.Sign.Properties._.IsRing.isCommutativeMonoid
d_isCommutativeMonoid_2116 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2116 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeMonoid_2116 v5
du_isCommutativeMonoid_2116 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2116 v0
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
-- Data.Sign.Properties._.IsRing.isCommutativeSemigroup
d_isCommutativeSemigroup_2118 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2118 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isCommutativeSemigroup_2118 v5
du_isCommutativeSemigroup_2118 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2118 v0
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
-- Data.Sign.Properties._.IsRing.isGroup
d_isGroup_2120 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_2120 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_2120 v5
du_isGroup_2120 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
du_isGroup_2120 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
         (coe v0))
-- Data.Sign.Properties._.IsRing.isInvertibleMagma
d_isInvertibleMagma_2122 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_2122 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleMagma_2122 v5
du_isInvertibleMagma_2122 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_2122 v0
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
-- Data.Sign.Properties._.IsRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2124 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2124 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isInvertibleUnitalMagma_2124 v5
du_isInvertibleUnitalMagma_2124 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2124 v0
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
-- Data.Sign.Properties._.IsRing.isMagma
d_isMagma_2126 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2126 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_2126 v5
du_isMagma_2126 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_2126 v0
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
-- Data.Sign.Properties._.IsRing.isMonoid
d_isMonoid_2128 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2128 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_2128 v5
du_isMonoid_2128 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_isMonoid_2128 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v0)))
-- Data.Sign.Properties._.IsRing.isSemigroup
d_isSemigroup_2130 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2130 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_2130 v5
du_isSemigroup_2130 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_2130 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
               (coe v0))))
-- Data.Sign.Properties._.IsRing.isUnitalMagma
d_isUnitalMagma_2132 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2132 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isUnitalMagma_2132 v5
du_isUnitalMagma_2132 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2132 v0
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
-- Data.Sign.Properties._.IsRing.⁻¹-cong
d_'8315''185''45'cong_2134 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2134 = erased
-- Data.Sign.Properties._.IsRing.inverse
d_inverse_2136 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2136 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_2136 v5
du_inverse_2136 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2136 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2762
            (coe v0)))
-- Data.Sign.Properties._.IsRing.inverseʳ
d_inverse'691'_2138 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_2138 = erased
-- Data.Sign.Properties._.IsRing.inverseˡ
d_inverse'737'_2140 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_2140 = erased
-- Data.Sign.Properties._.IsRing.distrib
d_distrib_2142 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2142 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2770 (coe v0)
-- Data.Sign.Properties._.IsRing.distribʳ
d_distrib'691'_2144 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2144 = erased
-- Data.Sign.Properties._.IsRing.distribˡ
d_distrib'737'_2146 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2146 = erased
-- Data.Sign.Properties._.IsRing.isEquivalence
d_isEquivalence_2148 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2148 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_2148 v5
du_isEquivalence_2148 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2148 v0
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
-- Data.Sign.Properties._.IsRing.isNearSemiring
d_isNearSemiring_2150 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2150 v0 v1 v2 v3 ~v4 v5
  = du_isNearSemiring_2150 v0 v1 v2 v3 v5
du_isNearSemiring_2150 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_2150 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v4))
-- Data.Sign.Properties._.IsRing.isPartialEquivalence
d_isPartialEquivalence_2152 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2152 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_2152 v5
du_isPartialEquivalence_2152 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2152 v0
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
-- Data.Sign.Properties._.IsRing.isRingWithoutOne
d_isRingWithoutOne_2154 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368
d_isRingWithoutOne_2154 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 v5
-- Data.Sign.Properties._.IsRing.isSemiring
d_isSemiring_2156 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_isSemiring_2156 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 v0 v1 v2 v3 v5
-- Data.Sign.Properties._.IsRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2158 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2158 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2868
      v5
-- Data.Sign.Properties._.IsRing.isSemiringWithoutOne
d_isSemiringWithoutOne_2160 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2160 v0 v1 v2 v3 ~v4 v5
  = du_isSemiringWithoutOne_2160 v0 v1 v2 v3 v5
du_isSemiringWithoutOne_2160 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
du_isSemiringWithoutOne_2160 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiring_2870 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Sign.Properties._.IsRing.refl
d_refl_2162 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2162 = erased
-- Data.Sign.Properties._.IsRing.reflexive
d_reflexive_2164 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2164 = erased
-- Data.Sign.Properties._.IsRing.setoid
d_setoid_2166 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2166 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_2166 v5
du_setoid_2166 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2166 v0
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
-- Data.Sign.Properties._.IsRing.sym
d_sym_2168 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2168 = erased
-- Data.Sign.Properties._.IsRing.trans
d_trans_2170 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2170 = erased
-- Data.Sign.Properties._.IsRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2172 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2172 = erased
-- Data.Sign.Properties._.IsRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2174 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2174 = erased
-- Data.Sign.Properties._.IsRing.zero
d_zero_2176 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2176 v0 v1 v2 v3 ~v4 v5 = du_zero_2176 v0 v1 v2 v3 v5
du_zero_2176 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_2176 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_zero_2468 (coe v0) (coe v1)
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2772 (coe v4))
-- Data.Sign.Properties._.IsRing.zeroʳ
d_zero'691'_2178 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2178 = erased
-- Data.Sign.Properties._.IsRing.zeroˡ
d_zero'737'_2180 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2740 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2180 = erased
-- Data.Sign.Properties._.IsRingWithoutOne._//_
d__'47''47'__2184 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
d__'47''47'__2184 v0 ~v1 v2 ~v3 ~v4 = du__'47''47'__2184 v0 v2
du__'47''47'__2184 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6
du__'47''47'__2184 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1136 (coe v0)
      (coe v1)
-- Data.Sign.Properties._.IsRingWithoutOne.*-assoc
d_'42''45'assoc_2186 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2186 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.*-cong
d_'42''45'cong_2188 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2188 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2190 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2190 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2192 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2192 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.*-isMagma
d_'42''45'isMagma_2194 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2194 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1324
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Sign.Properties._.IsRingWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2196 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2196 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1326
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Sign.Properties._.IsRingWithoutOne.assoc
d_assoc_2198 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2198 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.comm
d_comm_2200 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2200 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.∙-cong
d_'8729''45'cong_2202 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2202 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2204 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2204 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2206 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2206 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.identity
d_identity_2208 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2208 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
               (coe v0))))
-- Data.Sign.Properties._.IsRingWithoutOne.identityʳ
d_identity'691'_2210 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2210 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.identityˡ
d_identity'737'_2212 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2212 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2214 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'43''45'isAbelianGroup_2214 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
      (coe v0)
-- Data.Sign.Properties._.IsRingWithoutOne.isCommutativeMagma
d_isCommutativeMagma_2216 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2216 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2216 v4
du_isCommutativeMagma_2216 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2216 v0
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
-- Data.Sign.Properties._.IsRingWithoutOne.isCommutativeMonoid
d_isCommutativeMonoid_2218 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_2218 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMonoid_2218 v4
du_isCommutativeMonoid_2218 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_isCommutativeMonoid_2218 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
         (coe v0))
-- Data.Sign.Properties._.IsRingWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_2220 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2220 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2220 v4
du_isCommutativeSemigroup_2220 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2220 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1244
            (coe v1)))
-- Data.Sign.Properties._.IsRingWithoutOne.isGroup
d_isGroup_2222 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_isGroup_2222 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1184
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
         (coe v0))
-- Data.Sign.Properties._.IsRingWithoutOne.isInvertibleMagma
d_isInvertibleMagma_2224 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
d_isInvertibleMagma_2224 ~v0 ~v1 ~v2 ~v3 v4
  = du_isInvertibleMagma_2224 v4
du_isInvertibleMagma_2224 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_958
du_isInvertibleMagma_2224 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1160
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Sign.Properties._.IsRingWithoutOne.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_2226 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
d_isInvertibleUnitalMagma_2226 ~v0 ~v1 ~v2 ~v3 v4
  = du_isInvertibleUnitalMagma_2226 v4
du_isInvertibleUnitalMagma_2226 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_1012
du_isInvertibleUnitalMagma_2226 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1162
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1184 (coe v1)))
-- Data.Sign.Properties._.IsRingWithoutOne.isMagma
d_isMagma_2228 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2228 v0
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
-- Data.Sign.Properties._.IsRingWithoutOne.isMonoid
d_isMonoid_2230 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2230 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
            (coe v0)))
-- Data.Sign.Properties._.IsRingWithoutOne.isSemigroup
d_isSemigroup_2232 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2232 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1088
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1184
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
               (coe v0))))
-- Data.Sign.Properties._.IsRingWithoutOne.isUnitalMagma
d_isUnitalMagma_2234 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2234 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2234 v4
du_isUnitalMagma_2234 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2234 v0
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
-- Data.Sign.Properties._.IsRingWithoutOne.⁻¹-cong
d_'8315''185''45'cong_2236 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2236 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.inverse
d_inverse_2238 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2238 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1090
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1184
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2386
            (coe v0)))
-- Data.Sign.Properties._.IsRingWithoutOne.inverseʳ
d_inverse'691'_2240 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_2240 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.inverseˡ
d_inverse'737'_2242 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_2242 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.distrib
d_distrib_2244 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2244 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2392 (coe v0)
-- Data.Sign.Properties._.IsRingWithoutOne.distribʳ
d_distrib'691'_2246 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2246 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.distribˡ
d_distrib'737'_2248 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2248 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.isEquivalence
d_isEquivalence_2250 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2250 v0
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
-- Data.Sign.Properties._.IsRingWithoutOne.isNearSemiring
d_isNearSemiring_2252 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2252
  = coe MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2470
-- Data.Sign.Properties._.IsRingWithoutOne.isPartialEquivalence
d_isPartialEquivalence_2254 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2254 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2254 v4
du_isPartialEquivalence_2254 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2254 v0
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
-- Data.Sign.Properties._.IsRingWithoutOne.refl
d_refl_2256 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2256 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.reflexive
d_reflexive_2258 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2258 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.setoid
d_setoid_2260 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2260 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2260 v4
du_setoid_2260 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2260 v0
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
-- Data.Sign.Properties._.IsRingWithoutOne.sym
d_sym_2262 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2262 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.trans
d_trans_2264 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2264 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_2266 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'691''45''8315''185'_2266 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_2268 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'737''45''8315''185'_2268 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.zero
d_zero_2270 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2270 = coe MAlonzo.Code.Algebra.Structures.du_zero_2468
-- Data.Sign.Properties._.IsRingWithoutOne.zeroʳ
d_zero'691'_2272 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2272 = erased
-- Data.Sign.Properties._.IsRingWithoutOne.zeroˡ
d_zero'737'_2274 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2368 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2274 = erased
-- Data.Sign.Properties._.IsSelectiveMagma.isEquivalence
d_isEquivalence_2278 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2278 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0))
-- Data.Sign.Properties._.IsSelectiveMagma.isMagma
d_isMagma_2280 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2280 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0)
-- Data.Sign.Properties._.IsSelectiveMagma.isPartialEquivalence
d_isPartialEquivalence_2282 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2282 ~v0 v1
  = du_isPartialEquivalence_2282 v1
du_isPartialEquivalence_2282 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2282 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsSelectiveMagma.refl
d_refl_2284 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2284 = erased
-- Data.Sign.Properties._.IsSelectiveMagma.reflexive
d_reflexive_2286 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2286 = erased
-- Data.Sign.Properties._.IsSelectiveMagma.sel
d_sel_2288 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_2288 v0
  = coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0)
-- Data.Sign.Properties._.IsSelectiveMagma.setoid
d_setoid_2290 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2290 ~v0 v1 = du_setoid_2290 v1
du_setoid_2290 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2290 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0))
-- Data.Sign.Properties._.IsSelectiveMagma.sym
d_sym_2292 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2292 = erased
-- Data.Sign.Properties._.IsSelectiveMagma.trans
d_trans_2294 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2294 = erased
-- Data.Sign.Properties._.IsSelectiveMagma.∙-cong
d_'8729''45'cong_2296 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2296 = erased
-- Data.Sign.Properties._.IsSelectiveMagma.∙-congʳ
d_'8729''45'cong'691'_2298 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2298 = erased
-- Data.Sign.Properties._.IsSelectiveMagma.∙-congˡ
d_'8729''45'cong'737'_2300 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2300 = erased
-- Data.Sign.Properties._.IsSemigroup.assoc
d_assoc_2304 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2304 = erased
-- Data.Sign.Properties._.IsSemigroup.isEquivalence
d_isEquivalence_2306 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2306 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0))
-- Data.Sign.Properties._.IsSemigroup.isMagma
d_isMagma_2308 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2308 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Data.Sign.Properties._.IsSemigroup.isPartialEquivalence
d_isPartialEquivalence_2310 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2310 ~v0 v1
  = du_isPartialEquivalence_2310 v1
du_isPartialEquivalence_2310 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2310 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsSemigroup.refl
d_refl_2312 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2312 = erased
-- Data.Sign.Properties._.IsSemigroup.reflexive
d_reflexive_2314 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2314 = erased
-- Data.Sign.Properties._.IsSemigroup.setoid
d_setoid_2316 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2316 ~v0 v1 = du_setoid_2316 v1
du_setoid_2316 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2316 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0))
-- Data.Sign.Properties._.IsSemigroup.sym
d_sym_2318 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2318 = erased
-- Data.Sign.Properties._.IsSemigroup.trans
d_trans_2320 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2320 = erased
-- Data.Sign.Properties._.IsSemigroup.∙-cong
d_'8729''45'cong_2322 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2322 = erased
-- Data.Sign.Properties._.IsSemigroup.∙-congʳ
d_'8729''45'cong'691'_2324 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2324 = erased
-- Data.Sign.Properties._.IsSemigroup.∙-congˡ
d_'8729''45'cong'737'_2326 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2326 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.isEquivalence
d_isEquivalence_2330 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2330 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0))
-- Data.Sign.Properties._.IsSemimedialMagma.isMagma
d_isMagma_2332 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2332 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0)
-- Data.Sign.Properties._.IsSemimedialMagma.isPartialEquivalence
d_isPartialEquivalence_2334 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2334 ~v0 v1
  = du_isPartialEquivalence_2334 v1
du_isPartialEquivalence_2334 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2334 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsSemimedialMagma.refl
d_refl_2336 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2336 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.reflexive
d_reflexive_2338 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2338 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.semiMedial
d_semiMedial_2340 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_2340 v0
  = coe MAlonzo.Code.Algebra.Structures.d_semiMedial_418 (coe v0)
-- Data.Sign.Properties._.IsSemimedialMagma.semimedialʳ
d_semimedial'691'_2342 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'691'_2342 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.semimedialˡ
d_semimedial'737'_2344 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_semimedial'737'_2344 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.setoid
d_setoid_2346 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2346 ~v0 v1 = du_setoid_2346 v1
du_setoid_2346 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2346 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_416 (coe v0))
-- Data.Sign.Properties._.IsSemimedialMagma.sym
d_sym_2348 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2348 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.trans
d_trans_2350 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2350 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.∙-cong
d_'8729''45'cong_2352 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2352 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.∙-congʳ
d_'8729''45'cong'691'_2354 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2354 = erased
-- Data.Sign.Properties._.IsSemimedialMagma.∙-congˡ
d_'8729''45'cong'737'_2356 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_408 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2356 = erased
-- Data.Sign.Properties._.IsSemiring.*-assoc
d_'42''45'assoc_2360 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2360 = erased
-- Data.Sign.Properties._.IsSemiring.*-cong
d_'42''45'cong_2362 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2362 = erased
-- Data.Sign.Properties._.IsSemiring.∙-congʳ
d_'8729''45'cong'691'_2364 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2364 = erased
-- Data.Sign.Properties._.IsSemiring.∙-congˡ
d_'8729''45'cong'737'_2366 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2366 = erased
-- Data.Sign.Properties._.IsSemiring.*-identity
d_'42''45'identity_2368 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2368 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Sign.Properties._.IsSemiring.identityʳ
d_identity'691'_2370 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2370 = erased
-- Data.Sign.Properties._.IsSemiring.identityˡ
d_identity'737'_2372 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2372 = erased
-- Data.Sign.Properties._.IsSemiring.*-isMagma
d_'42''45'isMagma_2374 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2374 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMagma_2374 v4
du_'42''45'isMagma_2374 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'42''45'isMagma_2374 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Sign.Properties._.IsSemiring.*-isMonoid
d_'42''45'isMonoid_2376 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2376 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isMonoid_2376 v4
du_'42''45'isMonoid_2376 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'42''45'isMonoid_2376 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Sign.Properties._.IsSemiring.*-isSemigroup
d_'42''45'isSemigroup_2378 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2378 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'isSemigroup_2378 v4
du_'42''45'isSemigroup_2378 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'42''45'isSemigroup_2378 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Sign.Properties._.IsSemiring.assoc
d_assoc_2380 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2380 = erased
-- Data.Sign.Properties._.IsSemiring.comm
d_comm_2382 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2382 = erased
-- Data.Sign.Properties._.IsSemiring.∙-cong
d_'8729''45'cong_2384 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2384 = erased
-- Data.Sign.Properties._.IsSemiring.∙-congʳ
d_'8729''45'cong'691'_2386 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2386 = erased
-- Data.Sign.Properties._.IsSemiring.∙-congˡ
d_'8729''45'cong'737'_2388 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2388 = erased
-- Data.Sign.Properties._.IsSemiring.identity
d_identity_2390 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2390 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v0))))
-- Data.Sign.Properties._.IsSemiring.identityʳ
d_identity'691'_2392 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2392 = erased
-- Data.Sign.Properties._.IsSemiring.identityˡ
d_identity'737'_2394 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2394 = erased
-- Data.Sign.Properties._.IsSemiring.isCommutativeMagma
d_isCommutativeMagma_2396 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2396 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2396 v4
du_isCommutativeMagma_2396 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2396 v0
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
-- Data.Sign.Properties._.IsSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2398 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2398 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Sign.Properties._.IsSemiring.isCommutativeSemigroup
d_isCommutativeSemigroup_2400 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2400 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2400 v4
du_isCommutativeSemigroup_2400 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2400 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v1)))
-- Data.Sign.Properties._.IsSemiring.isMagma
d_isMagma_2402 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2402 v0
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
-- Data.Sign.Properties._.IsSemiring.isMonoid
d_isMonoid_2404 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2404 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
            (coe v0)))
-- Data.Sign.Properties._.IsSemiring.isSemigroup
d_isSemigroup_2406 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2406 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
               (coe v0))))
-- Data.Sign.Properties._.IsSemiring.isUnitalMagma
d_isUnitalMagma_2408 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2408 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2408 v4
du_isUnitalMagma_2408 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2408 v0
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
-- Data.Sign.Properties._.IsSemiring.distrib
d_distrib_2410 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2410 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1564
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
         (coe v0))
-- Data.Sign.Properties._.IsSemiring.distribʳ
d_distrib'691'_2412 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2412 = erased
-- Data.Sign.Properties._.IsSemiring.distribˡ
d_distrib'737'_2414 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2414 = erased
-- Data.Sign.Properties._.IsSemiring.isEquivalence
d_isEquivalence_2416 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2416 v0
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
-- Data.Sign.Properties._.IsSemiring.isNearSemiring
d_isNearSemiring_2418 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2418 ~v0 ~v1 ~v2 ~v3 v4
  = du_isNearSemiring_2418 v4
du_isNearSemiring_2418 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
du_isNearSemiring_2418 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730
         (coe v0))
-- Data.Sign.Properties._.IsSemiring.isPartialEquivalence
d_isPartialEquivalence_2420 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2420 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2420 v4
du_isPartialEquivalence_2420 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2420 v0
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
-- Data.Sign.Properties._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2422 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_isSemiringWithoutAnnihilatingZero_2422 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1654
      (coe v0)
-- Data.Sign.Properties._.IsSemiring.isSemiringWithoutOne
d_isSemiringWithoutOne_2424 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342
d_isSemiringWithoutOne_2424 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1730 v4
-- Data.Sign.Properties._.IsSemiring.refl
d_refl_2426 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2426 = erased
-- Data.Sign.Properties._.IsSemiring.reflexive
d_reflexive_2428 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2428 = erased
-- Data.Sign.Properties._.IsSemiring.setoid
d_setoid_2430 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2430 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2430 v4
du_setoid_2430 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2430 v0
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
-- Data.Sign.Properties._.IsSemiring.sym
d_sym_2432 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2432 = erased
-- Data.Sign.Properties._.IsSemiring.trans
d_trans_2434 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2434 = erased
-- Data.Sign.Properties._.IsSemiring.zero
d_zero_2436 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2436 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1656 (coe v0)
-- Data.Sign.Properties._.IsSemiring.zeroʳ
d_zero'691'_2438 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2438 = erased
-- Data.Sign.Properties._.IsSemiring.zeroˡ
d_zero'737'_2440 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2440 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2444 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2444 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2446 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2446 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congʳ
d_'8729''45'cong'691'_2448 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2448 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congˡ
d_'8729''45'cong'737'_2450 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2450 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2452 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2452 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1562 (coe v0)
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.identityʳ
d_identity'691'_2454 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2454 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.identityˡ
d_identity'737'_2456 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2456 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.*-isMagma
d_'42''45'isMagma_2458 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2458 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1614 v4
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.*-isMonoid
d_'42''45'isMonoid_2460 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2460 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_1618 v4
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.*-isSemigroup
d_'42''45'isSemigroup_2462 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2462 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1616 v4
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.assoc
d_assoc_2464 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2464 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.comm
d_comm_2466 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2466 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.∙-cong
d_'8729''45'cong_2468 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2468 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congʳ
d_'8729''45'cong'691'_2470 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2470 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.∙-congˡ
d_'8729''45'cong'737'_2472 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2472 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.identity
d_identity_2474 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2474 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v0)))
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.identityʳ
d_identity'691'_2476 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2476 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.identityˡ
d_identity'737'_2478 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2478 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.isCommutativeMagma
d_isCommutativeMagma_2480 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2480 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeMagma_2480 v4
du_isCommutativeMagma_2480 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2480 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2482 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2482 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
      (coe v0)
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.isCommutativeSemigroup
d_isCommutativeSemigroup_2484 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2484 ~v0 ~v1 ~v2 ~v3 v4
  = du_isCommutativeSemigroup_2484 v4
du_isCommutativeSemigroup_2484 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2484 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe v0))
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.isMagma
d_isMagma_2486 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2486 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
               (coe v0))))
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.isMonoid
d_isMonoid_2488 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2488 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
         (coe v0))
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.isSemigroup
d_isSemigroup_2490 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2490 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
            (coe v0)))
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.isUnitalMagma
d_isUnitalMagma_2492 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_2492 ~v0 ~v1 ~v2 ~v3 v4 = du_isUnitalMagma_2492 v4
du_isUnitalMagma_2492 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_2492 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1556
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v1)))
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2494 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2494 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1564 (coe v0)
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.distribʳ
d_distrib'691'_2496 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2496 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.distribˡ
d_distrib'737'_2498 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2498 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.isEquivalence
d_isEquivalence_2500 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2500 v0
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
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.isPartialEquivalence
d_isPartialEquivalence_2502 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2502 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_2502 v4
du_isPartialEquivalence_2502 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2502 v0
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
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.refl
d_refl_2504 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2504 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.reflexive
d_reflexive_2506 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2506 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.setoid
d_setoid_2508 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2508 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_2508 v4
du_setoid_2508 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2508 v0
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
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.sym
d_sym_2510 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2510 = erased
-- Data.Sign.Properties._.IsSemiringWithoutAnnihilatingZero.trans
d_trans_2512 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2512 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2516 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2516 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2518 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2518 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2520 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2520 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2522 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2522 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.*-isMagma
d_'42''45'isMagma_2524 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2524 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1410 v3
-- Data.Sign.Properties._.IsSemiringWithoutOne.*-isSemigroup
d_'42''45'isSemigroup_2526 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2526 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1412 v3
-- Data.Sign.Properties._.IsSemiringWithoutOne.assoc
d_assoc_2528 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2528 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.comm
d_comm_2530 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2530 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.∙-cong
d_'8729''45'cong_2532 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2532 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.∙-congʳ
d_'8729''45'cong'691'_2534 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2534 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.∙-congˡ
d_'8729''45'cong'737'_2536 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2536 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.identity
d_identity_2538 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2538 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
            (coe v0)))
-- Data.Sign.Properties._.IsSemiringWithoutOne.identityʳ
d_identity'691'_2540 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2540 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.identityˡ
d_identity'737'_2542 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2542 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.isCommutativeMagma
d_isCommutativeMagma_2544 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_2544 ~v0 ~v1 ~v2 v3
  = du_isCommutativeMagma_2544 v3
du_isCommutativeMagma_2544 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_2544 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
            (coe v1)))
-- Data.Sign.Properties._.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2546 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'43''45'isCommutativeMonoid_2546 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
      (coe v0)
-- Data.Sign.Properties._.IsSemiringWithoutOne.isCommutativeSemigroup
d_isCommutativeSemigroup_2548 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_2548 ~v0 ~v1 ~v2 v3
  = du_isCommutativeSemigroup_2548 v3
du_isCommutativeSemigroup_2548 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_2548 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe v0))
-- Data.Sign.Properties._.IsSemiringWithoutOne.isMonoid
d_isMonoid_2550 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_2550 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1360
         (coe v0))
-- Data.Sign.Properties._.IsSemiringWithoutOne.distrib
d_distrib_2552 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2552 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1366 (coe v0)
-- Data.Sign.Properties._.IsSemiringWithoutOne.distribʳ
d_distrib'691'_2554 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_2554 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.distribˡ
d_distrib'737'_2556 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'737'_2556 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.isEquivalence
d_isEquivalence_2558 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2558 v0
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
-- Data.Sign.Properties._.IsSemiringWithoutOne.isNearSemiring
d_isNearSemiring_2560 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1260
d_isNearSemiring_2560 v0 v1 v2 v3
  = coe MAlonzo.Code.Algebra.Structures.du_isNearSemiring_1428 v3
-- Data.Sign.Properties._.IsSemiringWithoutOne.isPartialEquivalence
d_isPartialEquivalence_2562 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2562 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_2562 v3
du_isPartialEquivalence_2562 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2562 v0
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
-- Data.Sign.Properties._.IsSemiringWithoutOne.refl
d_refl_2564 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2564 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.reflexive
d_reflexive_2566 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2566 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.setoid
d_setoid_2568 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2568 ~v0 ~v1 ~v2 v3 = du_setoid_2568 v3
du_setoid_2568 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2568 v0
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
-- Data.Sign.Properties._.IsSemiringWithoutOne.sym
d_sym_2570 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2570 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.trans
d_trans_2572 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2572 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.zero
d_zero_2574 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2574 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1368 (coe v0)
-- Data.Sign.Properties._.IsSemiringWithoutOne.zeroʳ
d_zero'691'_2576 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'691'_2576 = erased
-- Data.Sign.Properties._.IsSemiringWithoutOne.zeroˡ
d_zero'737'_2578 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1342 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_2578 = erased
-- Data.Sign.Properties._.IsSuccessorSet.isEquivalence
d_isEquivalence_2582 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2582 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_156 (coe v0)
-- Data.Sign.Properties._.IsSuccessorSet.isPartialEquivalence
d_isPartialEquivalence_2584 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2584 ~v0 ~v1 v2
  = du_isPartialEquivalence_2584 v2
du_isPartialEquivalence_2584 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2584 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
      (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_156 (coe v0))
-- Data.Sign.Properties._.IsSuccessorSet.refl
d_refl_2586 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2586 = erased
-- Data.Sign.Properties._.IsSuccessorSet.reflexive
d_reflexive_2588 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2588 = erased
-- Data.Sign.Properties._.IsSuccessorSet.setoid
d_setoid_2590 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2590 v0 v1 v2
  = coe MAlonzo.Code.Algebra.Structures.du_setoid_172 v2
-- Data.Sign.Properties._.IsSuccessorSet.suc#-cong
d_suc'35''45'cong_2592 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'35''45'cong_2592 = erased
-- Data.Sign.Properties._.IsSuccessorSet.sym
d_sym_2594 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2594 = erased
-- Data.Sign.Properties._.IsSuccessorSet.trans
d_trans_2596 ::
  MAlonzo.Code.Algebra.Structures.T_IsSuccessorSet_146 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2596 = erased
-- Data.Sign.Properties._.IsUnitalMagma.identity
d_identity_2600 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2600 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_678 (coe v0)
-- Data.Sign.Properties._.IsUnitalMagma.identityʳ
d_identity'691'_2602 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_2602 = erased
-- Data.Sign.Properties._.IsUnitalMagma.identityˡ
d_identity'737'_2604 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_2604 = erased
-- Data.Sign.Properties._.IsUnitalMagma.isEquivalence
d_isEquivalence_2606 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2606 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0))
-- Data.Sign.Properties._.IsUnitalMagma.isMagma
d_isMagma_2608 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2608 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0)
-- Data.Sign.Properties._.IsUnitalMagma.isPartialEquivalence
d_isPartialEquivalence_2610 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2610 ~v0 ~v1 v2
  = du_isPartialEquivalence_2610 v2
du_isPartialEquivalence_2610 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2610 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v1)))
-- Data.Sign.Properties._.IsUnitalMagma.refl
d_refl_2612 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_2612 = erased
-- Data.Sign.Properties._.IsUnitalMagma.reflexive
d_reflexive_2614 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_2614 = erased
-- Data.Sign.Properties._.IsUnitalMagma.setoid
d_setoid_2616 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2616 ~v0 ~v1 v2 = du_setoid_2616 v2
du_setoid_2616 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2616 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_setoid_202
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_676 (coe v0))
-- Data.Sign.Properties._.IsUnitalMagma.sym
d_sym_2618 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_2618 = erased
-- Data.Sign.Properties._.IsUnitalMagma.trans
d_trans_2620 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_2620 = erased
-- Data.Sign.Properties._.IsUnitalMagma.∙-cong
d_'8729''45'cong_2622 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2622 = erased
-- Data.Sign.Properties._.IsUnitalMagma.∙-congʳ
d_'8729''45'cong'691'_2624 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'691'_2624 = erased
-- Data.Sign.Properties._.IsUnitalMagma.∙-congˡ
d_'8729''45'cong'737'_2626 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong'737'_2626 = erased
-- Data.Sign.Properties._._Absorbs_
d__Absorbs__2630 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d__Absorbs__2630 = erased
-- Data.Sign.Properties._._DistributesOver_
d__DistributesOver__2632 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d__DistributesOver__2632 = erased
-- Data.Sign.Properties._._DistributesOverʳ_
d__DistributesOver'691'__2634 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d__DistributesOver'691'__2634 = erased
-- Data.Sign.Properties._._DistributesOverˡ_
d__DistributesOver'737'__2636 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d__DistributesOver'737'__2636 = erased
-- Data.Sign.Properties._._IdempotentOn_
d__IdempotentOn__2638 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 -> ()
d__IdempotentOn__2638 = erased
-- Data.Sign.Properties._._MiddleFourExchange_
d__MiddleFourExchange__2640 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d__MiddleFourExchange__2640 = erased
-- Data.Sign.Properties._.Absorptive
d_Absorptive_2642 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Absorptive_2642 = erased
-- Data.Sign.Properties._.AlmostCancellative
d_AlmostCancellative_2644 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_AlmostCancellative_2644 = erased
-- Data.Sign.Properties._.AlmostLeftCancellative
d_AlmostLeftCancellative_2646 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_AlmostLeftCancellative_2646 = erased
-- Data.Sign.Properties._.AlmostRightCancellative
d_AlmostRightCancellative_2648 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_AlmostRightCancellative_2648 = erased
-- Data.Sign.Properties._.Alternative
d_Alternative_2650 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Alternative_2650 = erased
-- Data.Sign.Properties._.Associative
d_Associative_2652 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Associative_2652 = erased
-- Data.Sign.Properties._.Cancellative
d_Cancellative_2654 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Cancellative_2654 = erased
-- Data.Sign.Properties._.Commutative
d_Commutative_2656 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Commutative_2656 = erased
-- Data.Sign.Properties._.Congruent₁
d_Congruent'8321'_2658 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Congruent'8321'_2658 = erased
-- Data.Sign.Properties._.Congruent₂
d_Congruent'8322'_2660 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Congruent'8322'_2660 = erased
-- Data.Sign.Properties._.Conical
d_Conical_2662 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Conical_2662 = erased
-- Data.Sign.Properties._.Flexible
d_Flexible_2664 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Flexible_2664 = erased
-- Data.Sign.Properties._.Idempotent
d_Idempotent_2666 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Idempotent_2666 = erased
-- Data.Sign.Properties._.IdempotentFun
d_IdempotentFun_2668 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_IdempotentFun_2668 = erased
-- Data.Sign.Properties._.Identical
d_Identical_2670 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Identical_2670 = erased
-- Data.Sign.Properties._.Identity
d_Identity_2672 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Identity_2672 = erased
-- Data.Sign.Properties._.Interchangable
d_Interchangable_2674 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Interchangable_2674 = erased
-- Data.Sign.Properties._.Inverse
d_Inverse_2676 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Inverse_2676 = erased
-- Data.Sign.Properties._.Invertible
d_Invertible_2678 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 -> ()
d_Invertible_2678 = erased
-- Data.Sign.Properties._.Involutive
d_Involutive_2680 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Involutive_2680 = erased
-- Data.Sign.Properties._.LeftAlternative
d_LeftAlternative_2682 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftAlternative_2682 = erased
-- Data.Sign.Properties._.LeftBol
d_LeftBol_2684 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftBol_2684 = erased
-- Data.Sign.Properties._.LeftCancellative
d_LeftCancellative_2686 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftCancellative_2686 = erased
-- Data.Sign.Properties._.LeftCongruent
d_LeftCongruent_2688 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftCongruent_2688 = erased
-- Data.Sign.Properties._.LeftConical
d_LeftConical_2690 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftConical_2690 = erased
-- Data.Sign.Properties._.LeftDivides
d_LeftDivides_2692 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftDivides_2692 = erased
-- Data.Sign.Properties._.LeftDividesʳ
d_LeftDivides'691'_2694 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftDivides'691'_2694 = erased
-- Data.Sign.Properties._.LeftDividesˡ
d_LeftDivides'737'_2696 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftDivides'737'_2696 = erased
-- Data.Sign.Properties._.LeftIdentity
d_LeftIdentity_2698 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftIdentity_2698 = erased
-- Data.Sign.Properties._.LeftInverse
d_LeftInverse_2700 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftInverse_2700 = erased
-- Data.Sign.Properties._.LeftInvertible
d_LeftInvertible_2702 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 -> ()
d_LeftInvertible_2702 = erased
-- Data.Sign.Properties._.LeftSemimedial
d_LeftSemimedial_2704 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftSemimedial_2704 = erased
-- Data.Sign.Properties._.LeftZero
d_LeftZero_2706 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_LeftZero_2706 = erased
-- Data.Sign.Properties._.Medial
d_Medial_2708 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Medial_2708 = erased
-- Data.Sign.Properties._.MiddleBol
d_MiddleBol_2710 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_MiddleBol_2710 = erased
-- Data.Sign.Properties._.RightAlternative
d_RightAlternative_2712 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightAlternative_2712 = erased
-- Data.Sign.Properties._.RightBol
d_RightBol_2714 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightBol_2714 = erased
-- Data.Sign.Properties._.RightCancellative
d_RightCancellative_2716 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightCancellative_2716 = erased
-- Data.Sign.Properties._.RightCongruent
d_RightCongruent_2718 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightCongruent_2718 = erased
-- Data.Sign.Properties._.RightConical
d_RightConical_2720 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightConical_2720 = erased
-- Data.Sign.Properties._.RightDivides
d_RightDivides_2722 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightDivides_2722 = erased
-- Data.Sign.Properties._.RightDividesʳ
d_RightDivides'691'_2724 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightDivides'691'_2724 = erased
-- Data.Sign.Properties._.RightDividesˡ
d_RightDivides'737'_2726 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightDivides'737'_2726 = erased
-- Data.Sign.Properties._.RightIdentity
d_RightIdentity_2728 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightIdentity_2728 = erased
-- Data.Sign.Properties._.RightInverse
d_RightInverse_2730 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightInverse_2730 = erased
-- Data.Sign.Properties._.RightInvertible
d_RightInvertible_2732 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 -> ()
d_RightInvertible_2732 = erased
-- Data.Sign.Properties._.RightSemimedial
d_RightSemimedial_2734 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightSemimedial_2734 = erased
-- Data.Sign.Properties._.RightZero
d_RightZero_2736 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_RightZero_2736 = erased
-- Data.Sign.Properties._.Selective
d_Selective_2738 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Selective_2738 = erased
-- Data.Sign.Properties._.SelfInverse
d_SelfInverse_2740 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_SelfInverse_2740 = erased
-- Data.Sign.Properties._.Semimedial
d_Semimedial_2742 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Semimedial_2742 = erased
-- Data.Sign.Properties._.StarDestructive
d_StarDestructive_2744 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_StarDestructive_2744 = erased
-- Data.Sign.Properties._.StarExpansive
d_StarExpansive_2746 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_StarExpansive_2746 = erased
-- Data.Sign.Properties._.StarLeftDestructive
d_StarLeftDestructive_2748 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_StarLeftDestructive_2748 = erased
-- Data.Sign.Properties._.StarLeftExpansive
d_StarLeftExpansive_2750 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_StarLeftExpansive_2750 = erased
-- Data.Sign.Properties._.StarRightDestructive
d_StarRightDestructive_2752 ::
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_StarRightDestructive_2752 = erased
-- Data.Sign.Properties._.StarRightExpansive
d_StarRightExpansive_2754 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_StarRightExpansive_2754 = erased
-- Data.Sign.Properties._.Zero
d_Zero_2756 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  (MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
   MAlonzo.Code.Data.Sign.Base.T_Sign_6) ->
  ()
d_Zero_2756 = erased
-- Data.Sign.Properties._≟_
d__'8799'__2758 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__2758 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sign.Base.C_'45'_8
        -> case coe v1 of
             MAlonzo.Code.Data.Sign.Base.C_'45'_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Data.Sign.Base.C_'43'_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sign.Base.C_'43'_10
        -> case coe v1 of
             MAlonzo.Code.Data.Sign.Base.C_'45'_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Data.Sign.Base.C_'43'_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sign.Properties.≡-setoid
d_'8801''45'setoid_2760 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_2760
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Sign.Properties.≡-decSetoid
d_'8801''45'decSetoid_2762 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_2762
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__2758)
-- Data.Sign.Properties.≡-isDecEquivalence
d_'8801''45'isDecEquivalence_2764 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_'8801''45'isDecEquivalence_2764
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isDecEquivalence_398
      (coe d__'8799'__2758)
-- Data.Sign.Properties.opposite-selfInverse
d_opposite'45'selfInverse_2766 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'selfInverse_2766 = erased
-- Data.Sign.Properties.opposite-involutive
d_opposite'45'involutive_2768 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'involutive_2768 = erased
-- Data.Sign.Properties.opposite-injective
d_opposite'45'injective_2770 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'injective_2770 = erased
-- Data.Sign.Properties.s≢opposite[s]
d_s'8802'opposite'91's'93'_2774 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_s'8802'opposite'91's'93'_2774 = erased
-- Data.Sign.Properties.s*s≡+
d_s'42's'8801''43'_2778 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s'42's'8801''43'_2778 = erased
-- Data.Sign.Properties.*-identityˡ
d_'42''45'identity'737'_2780 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_2780 = erased
-- Data.Sign.Properties.*-identityʳ
d_'42''45'identity'691'_2782 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_2782 = erased
-- Data.Sign.Properties.*-identity
d_'42''45'identity_2784 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2784
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Sign.Properties.*-comm
d_'42''45'comm_2786 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_2786 = erased
-- Data.Sign.Properties.*-assoc
d_'42''45'assoc_2788 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2788 = erased
-- Data.Sign.Properties.*-cancelʳ-≡
d_'42''45'cancel'691''45''8801'_2790 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'691''45''8801'_2790 = erased
-- Data.Sign.Properties.*-cancelˡ-≡
d_'42''45'cancel'737''45''8801'_2796 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45''8801'_2796 = erased
-- Data.Sign.Properties.*-cancel-≡
d_'42''45'cancel'45''8801'_2802 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'cancel'45''8801'_2802
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Sign.Properties.*-inverse
d_'42''45'inverse_2804 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'inverse_2804
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Sign.Properties.*-isMagma
d_'42''45'isMagma_2806 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'42''45'isMagma_2806
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Sign.Properties.*-magma
d_'42''45'magma_2808 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'42''45'magma_2808
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124
      MAlonzo.Code.Data.Sign.Base.d__'42'__14 d_'42''45'isMagma_2806
-- Data.Sign.Properties.*-isSemigroup
d_'42''45'isSemigroup_2810 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'42''45'isSemigroup_2810
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe d_'42''45'isMagma_2806) erased
-- Data.Sign.Properties.*-semigroup
d_'42''45'semigroup_2812 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'42''45'semigroup_2812
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614
      MAlonzo.Code.Data.Sign.Base.d__'42'__14 d_'42''45'isSemigroup_2810
-- Data.Sign.Properties.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_2814 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'42''45'isCommutativeSemigroup_2814
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_608
      (coe d_'42''45'isSemigroup_2810) erased
-- Data.Sign.Properties.*-commutativeSemigroup
d_'42''45'commutativeSemigroup_2816 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'42''45'commutativeSemigroup_2816
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_754
      MAlonzo.Code.Data.Sign.Base.d__'42'__14
      d_'42''45'isCommutativeSemigroup_2814
-- Data.Sign.Properties.*-isMonoid
d_'42''45'isMonoid_2818 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'42''45'isMonoid_2818
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe d_'42''45'isSemigroup_2810) (coe d_'42''45'identity_2784)
-- Data.Sign.Properties.*-monoid
d_'42''45'monoid_2820 :: MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'42''45'monoid_2820
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990
      MAlonzo.Code.Data.Sign.Base.d__'42'__14
      (coe MAlonzo.Code.Data.Sign.Base.C_'43'_10) d_'42''45'isMonoid_2818
-- Data.Sign.Properties.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_2822 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'42''45'isCommutativeMonoid_2822
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe d_'42''45'isMonoid_2818) erased
-- Data.Sign.Properties.*-commutativeMonoid
d_'42''45'commutativeMonoid_2824 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'42''45'commutativeMonoid_2824
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088
      MAlonzo.Code.Data.Sign.Base.d__'42'__14
      (coe MAlonzo.Code.Data.Sign.Base.C_'43'_10)
      d_'42''45'isCommutativeMonoid_2822
-- Data.Sign.Properties.*-isGroup
d_'42''45'isGroup_2826 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1074
d_'42''45'isGroup_2826
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1164
      (coe d_'42''45'isMonoid_2818) (coe d_'42''45'inverse_2804)
      (coe (\ v0 v1 v2 -> v2))
-- Data.Sign.Properties.*-group
d_'42''45'group_2828 :: MAlonzo.Code.Algebra.Bundles.T_Group_1564
d_'42''45'group_2828
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1676
      MAlonzo.Code.Data.Sign.Base.d__'42'__14
      (coe MAlonzo.Code.Data.Sign.Base.C_'43'_10) (\ v0 -> v0)
      d_'42''45'isGroup_2826
-- Data.Sign.Properties.*-isAbelianGroup
d_'42''45'isAbelianGroup_2830 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1172
d_'42''45'isAbelianGroup_2830
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1252
      (coe d_'42''45'isGroup_2826) erased
-- Data.Sign.Properties.*-abelianGroup
d_'42''45'abelianGroup_2832 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1682
d_'42''45'abelianGroup_2832
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1808
      MAlonzo.Code.Data.Sign.Base.d__'42'__14
      (coe MAlonzo.Code.Data.Sign.Base.C_'43'_10) (\ v0 -> v0)
      d_'42''45'isAbelianGroup_2830
-- Data.Sign.Properties.s*opposite[s]≡-
d_s'42'opposite'91's'93''8801''45'_2836 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s'42'opposite'91's'93''8801''45'_2836 = erased
-- Data.Sign.Properties.opposite[s]*s≡-
d_opposite'91's'93''42's'8801''45'_2840 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'91's'93''42's'8801''45'_2840 = erased
