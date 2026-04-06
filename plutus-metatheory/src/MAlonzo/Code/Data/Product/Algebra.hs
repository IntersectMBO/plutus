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

module MAlonzo.Code.Data.Product.Algebra where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Empty.Polymorphic
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Algebra
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Unit.Polymorphic.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Properties.Inverse

-- Data.Product.Algebra.Σ-assoc
d_Σ'45'assoc_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_Σ'45'assoc_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_Σ'45'assoc_32
du_Σ'45'assoc_32 :: MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_Σ'45'assoc_32
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Product.Base.du_assoc'691'_260)
      (coe MAlonzo.Code.Data.Product.Base.du_assoc'737'_276)
-- Data.Product.Algebra.Σ-assoc-alt
d_Σ'45'assoc'45'alt_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_Σ'45'assoc'45'alt_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_Σ'45'assoc'45'alt_40
du_Σ'45'assoc'45'alt_40 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_Σ'45'assoc'45'alt_40
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Product.Base.du_assoc'691''45'curried_290)
      (coe MAlonzo.Code.Data.Product.Base.du_assoc'737''45'curried_304)
-- Data.Product.Algebra.×-cong
d_'215''45'cong_42 ::
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
d_'215''45'cong_42 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_'215''45'cong_42 v8 v9
du_'215''45'cong_42 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'cong_42 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_2134 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_2136 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_2136 (coe v1))))
-- Data.Product.Algebra.×-comm
d_'215''45'comm_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'215''45'comm_232 ~v0 ~v1 ~v2 ~v3 = du_'215''45'comm_232
du_'215''45'comm_232 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'comm_232
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Product.Base.du_swap_370)
      (coe MAlonzo.Code.Data.Product.Base.du_swap_370)
-- Data.Product.Algebra._.×-assoc
d_'215''45'assoc_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'215''45'assoc_240 ~v0 ~v1 ~v2 ~v3 = du_'215''45'assoc_240
du_'215''45'assoc_240 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'assoc_240
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Product.Base.du_assoc'691''8242'_388)
      (coe MAlonzo.Code.Data.Product.Base.du_assoc'737''8242'_396)
-- Data.Product.Algebra._.×-identityˡ
d_'215''45'identity'737'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'215''45'identity'737'_242 ~v0 ~v1
  = du_'215''45'identity'737'_242
du_'215''45'identity'737'_242 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'identity'737'_242
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Data.Unit.Polymorphic.Base.du_tt_16) (coe v0)))
-- Data.Product.Algebra._.×-identityʳ
d_'215''45'identity'691'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'215''45'identity'691'_246 ~v0 ~v1
  = du_'215''45'identity'691'_246
du_'215''45'identity'691'_246 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'identity'691'_246
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
              (coe MAlonzo.Code.Data.Unit.Polymorphic.Base.du_tt_16)))
-- Data.Product.Algebra._.×-identity
d_'215''45'identity_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'identity_250 ~v0 = du_'215''45'identity_250
du_'215''45'identity_250 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'identity_250
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'215''45'identity'737'_242)
      (\ v0 -> coe du_'215''45'identity'691'_246)
-- Data.Product.Algebra._.×-zeroˡ
d_'215''45'zero'737'_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'215''45'zero'737'_252 ~v0 ~v1 = du_'215''45'zero'737'_252
du_'215''45'zero'737'_252 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'zero'737'_252
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (\ v0 ->
         coe MAlonzo.Code.Data.Empty.Polymorphic.du_'8869''45'elim_20)
-- Data.Product.Algebra._.×-zeroʳ
d_'215''45'zero'691'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'215''45'zero'691'_256 ~v0 ~v1 = du_'215''45'zero'691'_256
du_'215''45'zero'691'_256 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'zero'691'_256
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (\ v0 ->
         coe MAlonzo.Code.Data.Empty.Polymorphic.du_'8869''45'elim_20)
-- Data.Product.Algebra._.×-zero
d_'215''45'zero_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'zero_260 ~v0 = du_'215''45'zero_260
du_'215''45'zero_260 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'zero_260
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'215''45'zero'737'_252)
      (\ v0 -> coe du_'215''45'zero'691'_256)
-- Data.Product.Algebra._.×-distribˡ-⊎
d_'215''45'distrib'737''45''8846'_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'215''45'distrib'737''45''8846'_262 ~v0 ~v1 ~v2 ~v3
  = du_'215''45'distrib'737''45''8846'_262
du_'215''45'distrib'737''45''8846'_262 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'distrib'737''45''8846'_262
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (coe
            (\ v0 ->
               coe
                 MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                 (coe
                    MAlonzo.Code.Function.Base.du__'8728''8242'__216
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe
                       (\ v1 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))))
                 (coe
                    MAlonzo.Code.Function.Base.du__'8728''8242'__216
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe
                       (\ v1 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)))))))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
         (coe
            MAlonzo.Code.Data.Product.Base.du_map'8322'_150
            (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)))
         (coe
            MAlonzo.Code.Data.Product.Base.du_map'8322'_150
            (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42))))
-- Data.Product.Algebra._.×-distribʳ-⊎
d_'215''45'distrib'691''45''8846'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'215''45'distrib'691''45''8846'_272 ~v0 ~v1 ~v2 ~v3
  = du_'215''45'distrib'691''45''8846'_272
du_'215''45'distrib'691''45''8846'_272 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'215''45'distrib'691''45''8846'_272
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (coe
            MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
            (coe
               MAlonzo.Code.Data.Product.Base.du_curry_224
               (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
            (coe
               MAlonzo.Code.Data.Product.Base.du_curry_224
               (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42))))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
         (coe
            MAlonzo.Code.Data.Product.Base.du_map'8321'_138
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
         (coe
            MAlonzo.Code.Data.Product.Base.du_map'8321'_138
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)))
-- Data.Product.Algebra._.×-distrib-⊎
d_'215''45'distrib'45''8846'_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'distrib'45''8846'_278 ~v0
  = du_'215''45'distrib'45''8846'_278
du_'215''45'distrib'45''8846'_278 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'distrib'45''8846'_278
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 -> coe du_'215''45'distrib'737''45''8846'_262)
      (\ v0 v1 v2 -> coe du_'215''45'distrib'691''45''8846'_272)
-- Data.Product.Algebra._.×-isMagma
d_'215''45'isMagma_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'215''45'isMagma_280 ~v0 = du_'215''45'isMagma_280
du_'215''45'isMagma_280 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'215''45'isMagma_280
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Function.Properties.Inverse.du_'8596''45'isEquivalence_42)
      (coe (\ v0 v1 v2 v3 v4 v5 -> coe du_'215''45'cong_42 v4 v5))
-- Data.Product.Algebra._.×-isSemigroup
d_'215''45'isSemigroup_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'215''45'isSemigroup_282 ~v0 = du_'215''45'isSemigroup_282
du_'215''45'isSemigroup_282 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'215''45'isSemigroup_282
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe du_'215''45'isMagma_280)
      (coe (\ v0 v1 v2 -> coe du_Σ'45'assoc_32))
-- Data.Product.Algebra._.×-isMonoid
d_'215''45'isMonoid_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'215''45'isMonoid_290 ~v0 = du_'215''45'isMonoid_290
du_'215''45'isMonoid_290 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'215''45'isMonoid_290
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe du_'215''45'isSemigroup_282)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (\ v0 -> coe du_'215''45'identity'737'_242)
         (\ v0 -> coe du_'215''45'identity'691'_246))
-- Data.Product.Algebra._.×-isCommutativeMonoid
d_'215''45'isCommutativeMonoid_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_'215''45'isCommutativeMonoid_292 ~v0
  = du_'215''45'isCommutativeMonoid_292
du_'215''45'isCommutativeMonoid_292 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
du_'215''45'isCommutativeMonoid_292
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_820
      (coe du_'215''45'isMonoid_290)
      (\ v0 v1 -> coe du_'215''45'comm_232)
-- Data.Product.Algebra._.⊎-×-isSemiringWithoutAnnihilatingZero
d_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
d_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_294 ~v0
  = du_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_294
du_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_294 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1536
du_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_294
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1630
      (coe
         MAlonzo.Code.Data.Sum.Algebra.du_'8846''45'isCommutativeMonoid_230)
      (coe (\ v0 v1 v2 v3 v4 v5 -> coe du_'215''45'cong_42 v4 v5))
      (\ v0 v1 v2 -> coe du_'215''45'assoc_240)
      (coe du_'215''45'identity_250)
      (coe du_'215''45'distrib'45''8846'_278)
-- Data.Product.Algebra._.⊎-×-isSemiring
d_'8846''45''215''45'isSemiring_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
d_'8846''45''215''45'isSemiring_296 ~v0
  = du_'8846''45''215''45'isSemiring_296
du_'8846''45''215''45'isSemiring_296 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1640
du_'8846''45''215''45'isSemiring_296
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1740
      (coe du_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_294)
      (coe du_'215''45'zero_260)
-- Data.Product.Algebra._.⊎-×-isCommutativeSemiring
d_'8846''45''215''45'isCommutativeSemiring_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
d_'8846''45''215''45'isCommutativeSemiring_298 ~v0
  = du_'8846''45''215''45'isCommutativeSemiring_298
du_'8846''45''215''45'isCommutativeSemiring_298 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1750
du_'8846''45''215''45'isCommutativeSemiring_298
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_1862
      (coe du_'8846''45''215''45'isSemiring_296)
      (\ v0 v1 -> coe du_'215''45'comm_232)
-- Data.Product.Algebra._.×-magma
d_'215''45'magma_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'215''45'magma_300 ~v0 = du_'215''45'magma_300
du_'215''45'magma_300 :: MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_'215''45'magma_300
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124 erased
      (coe du_'215''45'isMagma_280)
-- Data.Product.Algebra._.×-semigroup
d_'215''45'semigroup_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'215''45'semigroup_302 ~v0 = du_'215''45'semigroup_302
du_'215''45'semigroup_302 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_'215''45'semigroup_302
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614 erased
      (coe du_'215''45'isSemigroup_282)
-- Data.Product.Algebra._.×-monoid
d_'215''45'monoid_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'215''45'monoid_304 ~v0 = du_'215''45'monoid_304
du_'215''45'monoid_304 :: MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'215''45'monoid_304
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990 erased erased
      (coe du_'215''45'isMonoid_290)
-- Data.Product.Algebra._.×-commutativeMonoid
d_'215''45'commutativeMonoid_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
d_'215''45'commutativeMonoid_306 ~v0
  = du_'215''45'commutativeMonoid_306
du_'215''45'commutativeMonoid_306 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_996
du_'215''45'commutativeMonoid_306
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_1088 erased erased
      (coe du_'215''45'isCommutativeMonoid_292)
-- Data.Product.Algebra._.×-⊎-commutativeSemiring
d_'215''45''8846''45'commutativeSemiring_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
d_'215''45''8846''45'commutativeSemiring_308 ~v0
  = du_'215''45''8846''45'commutativeSemiring_308
du_'215''45''8846''45'commutativeSemiring_308 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2524
du_'215''45''8846''45'commutativeSemiring_308
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_2706 erased erased
      erased erased (coe du_'8846''45''215''45'isCommutativeSemiring_298)
