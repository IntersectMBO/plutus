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

module MAlonzo.Code.Data.Sum.Algebra where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Properties.Inverse
import qualified MAlonzo.Code.Level

-- Data.Sum.Algebra.♯
d_'9839'_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Level.T_Lift_8 -> ()) ->
  MAlonzo.Code.Level.T_Lift_8 -> AgdaAny
d_'9839'_26 ~v0 ~v1 ~v2 ~v3 = du_'9839'_26
du_'9839'_26 :: AgdaAny
du_'9839'_26 = MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Algebra.⊎-cong
d_'8846''45'cong_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8846''45'cong_28 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_'8846''45'cong_28 v8 v9
du_'8846''45'cong_28 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8846''45'cong_28 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_from_2136 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_2136 (coe v1)))
-- Data.Sum.Algebra.⊎-comm
d_'8846''45'comm_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8846''45'comm_206 ~v0 ~v1 ~v2 ~v3 = du_'8846''45'comm_206
du_'8846''45'comm_206 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8846''45'comm_206
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Sum.Base.du_swap_78)
      (coe MAlonzo.Code.Data.Sum.Base.du_swap_78)
-- Data.Sum.Algebra._.⊎-assoc
d_'8846''45'assoc_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8846''45'assoc_214 ~v0 ~v1 ~v2 ~v3 = du_'8846''45'assoc_214
du_'8846''45'assoc_214 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8846''45'assoc_214
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Sum.Base.du_assoc'691'_96)
      (coe MAlonzo.Code.Data.Sum.Base.du_assoc'737'_98)
-- Data.Sum.Algebra._.⊎-identityˡ
d_'8846''45'identity'737'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8846''45'identity'737'_216 ~v0 ~v1
  = du_'8846''45'identity'737'_216
du_'8846''45'identity'737'_216 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8846''45'identity'737'_216
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
         (\ v0 -> coe du_'9839'_26) (coe (\ v0 -> v0)))
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
-- Data.Sum.Algebra._.⊎-identityʳ
d_'8846''45'identity'691'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8846''45'identity'691'_220 ~v0 ~v1
  = du_'8846''45'identity'691'_220
du_'8846''45'identity'691'_220 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8846''45'identity'691'_220
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52 (coe (\ v0 -> v0))
         (\ v0 -> coe du_'9839'_26))
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
-- Data.Sum.Algebra._.⊎-identity
d_'8846''45'identity_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8846''45'identity_222 ~v0 = du_'8846''45'identity_222
du_'8846''45'identity_222 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8846''45'identity_222
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'8846''45'identity'737'_216)
      (\ v0 -> coe du_'8846''45'identity'691'_220)
-- Data.Sum.Algebra._.⊎-isMagma
d_'8846''45'isMagma_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8846''45'isMagma_224 ~v0 = du_'8846''45'isMagma_224
du_'8846''45'isMagma_224 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8846''45'isMagma_224
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Function.Properties.Inverse.du_'8596''45'isEquivalence_42)
      (coe (\ v0 v1 v2 v3 v4 v5 -> coe du_'8846''45'cong_28 v4 v5))
-- Data.Sum.Algebra._.⊎-isSemigroup
d_'8846''45'isSemigroup_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8846''45'isSemigroup_226 ~v0 = du_'8846''45'isSemigroup_226
du_'8846''45'isSemigroup_226 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8846''45'isSemigroup_226
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe du_'8846''45'isMagma_224)
      (\ v0 v1 v2 -> coe du_'8846''45'assoc_214)
-- Data.Sum.Algebra._.⊎-isMonoid
d_'8846''45'isMonoid_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8846''45'isMonoid_228 ~v0 = du_'8846''45'isMonoid_228
du_'8846''45'isMonoid_228 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8846''45'isMonoid_228
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe du_'8846''45'isSemigroup_226)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (\ v0 -> coe du_'8846''45'identity'737'_216)
         (\ v0 -> coe du_'8846''45'identity'691'_220))
-- Data.Sum.Algebra._.⊎-isCommutativeMonoid
d_'8846''45'isCommutativeMonoid_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'8846''45'isCommutativeMonoid_230 ~v0
  = du_'8846''45'isCommutativeMonoid_230
du_'8846''45'isCommutativeMonoid_230 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'8846''45'isCommutativeMonoid_230
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe du_'8846''45'isMonoid_228)
      (\ v0 v1 -> coe du_'8846''45'comm_206)
-- Data.Sum.Algebra._.⊎-magma
d_'8846''45'magma_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8846''45'magma_232 ~v0 = du_'8846''45'magma_232
du_'8846''45'magma_232 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_'8846''45'magma_232
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124 erased
      (coe du_'8846''45'isMagma_224)
-- Data.Sum.Algebra._.⊎-semigroup
d_'8846''45'semigroup_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8846''45'semigroup_234 ~v0 = du_'8846''45'semigroup_234
du_'8846''45'semigroup_234 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_'8846''45'semigroup_234
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614 erased
      (coe du_'8846''45'isSemigroup_226)
-- Data.Sum.Algebra._.⊎-monoid
d_'8846''45'monoid_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8846''45'monoid_236 ~v0 = du_'8846''45'monoid_236
du_'8846''45'monoid_236 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'8846''45'monoid_236
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990 erased erased
      (coe du_'8846''45'isMonoid_228)
-- Data.Sum.Algebra._.⊎-commutativeMonoid
d_'8846''45'commutativeMonoid_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'8846''45'commutativeMonoid_238 ~v0
  = du_'8846''45'commutativeMonoid_238
du_'8846''45'commutativeMonoid_238 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
du_'8846''45'commutativeMonoid_238
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088 erased erased
      (coe du_'8846''45'isCommutativeMonoid_230)
