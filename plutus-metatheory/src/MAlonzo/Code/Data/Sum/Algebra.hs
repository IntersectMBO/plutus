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

module MAlonzo.Code.Data.Sum.Algebra where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Properties.Inverse qualified
import MAlonzo.Code.Level qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'cong_28 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_'8846''45'cong_28 v8 v9
du_'8846''45'cong_28 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'cong_28 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v1)))
-- Data.Sum.Algebra.⊎-comm
d_'8846''45'comm_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'comm_198 ~v0 ~v1 ~v2 ~v3 = du_'8846''45'comm_198
du_'8846''45'comm_198 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'comm_198
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Sum.Base.du_swap_78)
      (coe MAlonzo.Code.Data.Sum.Base.du_swap_78)
-- Data.Sum.Algebra._.⊎-assoc
d_'8846''45'assoc_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'assoc_206 ~v0 ~v1 ~v2 ~v3 = du_'8846''45'assoc_206
du_'8846''45'assoc_206 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'assoc_206
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Sum.Base.du_assoc'691'_96)
      (coe MAlonzo.Code.Data.Sum.Base.du_assoc'737'_98)
-- Data.Sum.Algebra._.⊎-identityˡ
d_'8846''45'identity'737'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'identity'737'_208 ~v0 ~v1
  = du_'8846''45'identity'737'_208
du_'8846''45'identity'737'_208 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'identity'737'_208
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
         (\ v0 -> coe du_'9839'_26) (coe (\ v0 -> v0)))
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
-- Data.Sum.Algebra._.⊎-identityʳ
d_'8846''45'identity'691'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'identity'691'_212 ~v0 ~v1
  = du_'8846''45'identity'691'_212
du_'8846''45'identity'691'_212 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'identity'691'_212
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52 (coe (\ v0 -> v0))
         (\ v0 -> coe du_'9839'_26))
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
-- Data.Sum.Algebra._.⊎-identity
d_'8846''45'identity_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8846''45'identity_214 ~v0 = du_'8846''45'identity_214
du_'8846''45'identity_214 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8846''45'identity_214
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'8846''45'identity'737'_208)
      (\ v0 -> coe du_'8846''45'identity'691'_212)
-- Data.Sum.Algebra._.⊎-isMagma
d_'8846''45'isMagma_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8846''45'isMagma_216 ~v0 = du_'8846''45'isMagma_216
du_'8846''45'isMagma_216 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8846''45'isMagma_216
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Function.Properties.Inverse.du_'8596''45'isEquivalence_42)
      (coe (\ v0 v1 v2 v3 v4 v5 -> coe du_'8846''45'cong_28 v4 v5))
-- Data.Sum.Algebra._.⊎-isSemigroup
d_'8846''45'isSemigroup_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8846''45'isSemigroup_218 ~v0 = du_'8846''45'isSemigroup_218
du_'8846''45'isSemigroup_218 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8846''45'isSemigroup_218
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe du_'8846''45'isMagma_216)
      (\ v0 v1 v2 -> coe du_'8846''45'assoc_206)
-- Data.Sum.Algebra._.⊎-isMonoid
d_'8846''45'isMonoid_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8846''45'isMonoid_220 ~v0 = du_'8846''45'isMonoid_220
du_'8846''45'isMonoid_220 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8846''45'isMonoid_220
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe du_'8846''45'isSemigroup_218)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (\ v0 -> coe du_'8846''45'identity'737'_208)
         (\ v0 -> coe du_'8846''45'identity'691'_212))
-- Data.Sum.Algebra._.⊎-isCommutativeMonoid
d_'8846''45'isCommutativeMonoid_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'8846''45'isCommutativeMonoid_222 ~v0
  = du_'8846''45'isCommutativeMonoid_222
du_'8846''45'isCommutativeMonoid_222 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_'8846''45'isCommutativeMonoid_222
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe du_'8846''45'isMonoid_220)
      (\ v0 v1 -> coe du_'8846''45'comm_198)
-- Data.Sum.Algebra._.⊎-magma
d_'8846''45'magma_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8846''45'magma_224 ~v0 = du_'8846''45'magma_224
du_'8846''45'magma_224 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_'8846''45'magma_224
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1279 erased
      (coe du_'8846''45'isMagma_216)
-- Data.Sum.Algebra._.⊎-semigroup
d_'8846''45'semigroup_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8846''45'semigroup_226 ~v0 = du_'8846''45'semigroup_226
du_'8846''45'semigroup_226 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'8846''45'semigroup_226
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9793 erased
      (coe du_'8846''45'isSemigroup_218)
-- Data.Sum.Algebra._.⊎-monoid
d_'8846''45'monoid_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'8846''45'monoid_228 ~v0 = du_'8846''45'monoid_228
du_'8846''45'monoid_228 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'8846''45'monoid_228
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16157 erased
      erased (coe du_'8846''45'isMonoid_220)
-- Data.Sum.Algebra._.⊎-commutativeMonoid
d_'8846''45'commutativeMonoid_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'8846''45'commutativeMonoid_230 ~v0
  = du_'8846''45'commutativeMonoid_230
du_'8846''45'commutativeMonoid_230 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
du_'8846''45'commutativeMonoid_230
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17931
      erased erased (coe du_'8846''45'isCommutativeMonoid_222)
