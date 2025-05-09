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

module MAlonzo.Code.Data.Product.Algebra where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Data.Empty.Polymorphic qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.Sum.Algebra qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Data.Unit.Polymorphic.Base qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Properties.Inverse qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Product.Algebra.Σ-assoc
d_Σ'45'assoc_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_Σ'45'assoc_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_Σ'45'assoc_32
du_Σ'45'assoc_32 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_Σ'45'assoc_32
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
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
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_Σ'45'assoc'45'alt_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_Σ'45'assoc'45'alt_40
du_Σ'45'assoc'45'alt_40 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_Σ'45'assoc'45'alt_40
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
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
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'cong_42 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_'215''45'cong_42 v8 v9
du_'215''45'cong_42 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'cong_42 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1972 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_1974 (coe v1))))
-- Data.Product.Algebra.×-comm
d_'215''45'comm_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'comm_224 ~v0 ~v1 ~v2 ~v3 = du_'215''45'comm_224
du_'215''45'comm_224 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'comm_224
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Product.Base.du_swap_370)
      (coe MAlonzo.Code.Data.Product.Base.du_swap_370)
-- Data.Product.Algebra._.×-assoc
d_'215''45'assoc_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'assoc_232 ~v0 ~v1 ~v2 ~v3 = du_'215''45'assoc_232
du_'215''45'assoc_232 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'assoc_232
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Product.Base.du_assoc'691''8242'_388)
      (coe MAlonzo.Code.Data.Product.Base.du_assoc'737''8242'_396)
-- Data.Product.Algebra._.×-identityˡ
d_'215''45'identity'737'_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'identity'737'_234 ~v0 ~v1
  = du_'215''45'identity'737'_234
du_'215''45'identity'737'_234 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'identity'737'_234
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Data.Unit.Polymorphic.Base.du_tt_16) (coe v0)))
-- Data.Product.Algebra._.×-identityʳ
d_'215''45'identity'691'_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'identity'691'_238 ~v0 ~v1
  = du_'215''45'identity'691'_238
du_'215''45'identity'691'_238 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'identity'691'_238
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
              (coe MAlonzo.Code.Data.Unit.Polymorphic.Base.du_tt_16)))
-- Data.Product.Algebra._.×-identity
d_'215''45'identity_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'identity_242 ~v0 = du_'215''45'identity_242
du_'215''45'identity_242 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'identity_242
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'215''45'identity'737'_234)
      (\ v0 -> coe du_'215''45'identity'691'_238)
-- Data.Product.Algebra._.×-zeroˡ
d_'215''45'zero'737'_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'zero'737'_244 ~v0 ~v1 = du_'215''45'zero'737'_244
du_'215''45'zero'737'_244 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'zero'737'_244
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (\ v0 ->
         coe MAlonzo.Code.Data.Empty.Polymorphic.du_'8869''45'elim_20)
-- Data.Product.Algebra._.×-zeroʳ
d_'215''45'zero'691'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'zero'691'_248 ~v0 ~v1 = du_'215''45'zero'691'_248
du_'215''45'zero'691'_248 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'zero'691'_248
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (\ v0 ->
         coe MAlonzo.Code.Data.Empty.Polymorphic.du_'8869''45'elim_20)
-- Data.Product.Algebra._.×-zero
d_'215''45'zero_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'zero_252 ~v0 = du_'215''45'zero_252
du_'215''45'zero_252 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'zero_252
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'215''45'zero'737'_244)
      (\ v0 -> coe du_'215''45'zero'691'_248)
-- Data.Product.Algebra._.×-distribˡ-⊎
d_'215''45'distrib'737''45''8846'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'distrib'737''45''8846'_254 ~v0 ~v1 ~v2 ~v3
  = du_'215''45'distrib'737''45''8846'_254
du_'215''45'distrib'737''45''8846'_254 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'distrib'737''45''8846'_254
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
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
d_'215''45'distrib'691''45''8846'_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'distrib'691''45''8846'_264 ~v0 ~v1 ~v2 ~v3
  = du_'215''45'distrib'691''45''8846'_264
du_'215''45'distrib'691''45''8846'_264 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'distrib'691''45''8846'_264
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
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
d_'215''45'distrib'45''8846'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'distrib'45''8846'_270 ~v0
  = du_'215''45'distrib'45''8846'_270
du_'215''45'distrib'45''8846'_270 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'distrib'45''8846'_270
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 -> coe du_'215''45'distrib'737''45''8846'_254)
      (\ v0 v1 v2 -> coe du_'215''45'distrib'691''45''8846'_264)
-- Data.Product.Algebra._.×-isMagma
d_'215''45'isMagma_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'215''45'isMagma_272 ~v0 = du_'215''45'isMagma_272
du_'215''45'isMagma_272 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'215''45'isMagma_272
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Function.Properties.Inverse.du_'8596''45'isEquivalence_42)
      (coe (\ v0 v1 v2 v3 v4 v5 -> coe du_'215''45'cong_42 v4 v5))
-- Data.Product.Algebra._.×-isSemigroup
d_'215''45'isSemigroup_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'215''45'isSemigroup_274 ~v0 = du_'215''45'isSemigroup_274
du_'215''45'isSemigroup_274 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'215''45'isSemigroup_274
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe du_'215''45'isMagma_272)
      (coe (\ v0 v1 v2 -> coe du_Σ'45'assoc_32))
-- Data.Product.Algebra._.×-isMonoid
d_'215''45'isMonoid_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'215''45'isMonoid_282 ~v0 = du_'215''45'isMonoid_282
du_'215''45'isMonoid_282 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'215''45'isMonoid_282
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe du_'215''45'isSemigroup_274)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (\ v0 -> coe du_'215''45'identity'737'_234)
         (\ v0 -> coe du_'215''45'identity'691'_238))
-- Data.Product.Algebra._.×-isCommutativeMonoid
d_'215''45'isCommutativeMonoid_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'215''45'isCommutativeMonoid_284 ~v0
  = du_'215''45'isCommutativeMonoid_284
du_'215''45'isCommutativeMonoid_284 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_'215''45'isCommutativeMonoid_284
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe du_'215''45'isMonoid_282)
      (\ v0 v1 -> coe du_'215''45'comm_224)
-- Data.Product.Algebra._.⊎-×-isSemiringWithoutAnnihilatingZero
d_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_286 ~v0
  = du_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_286
du_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_286 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
du_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_286
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43811
      (coe
         MAlonzo.Code.Data.Sum.Algebra.du_'8846''45'isCommutativeMonoid_222)
      (coe (\ v0 v1 v2 v3 v4 v5 -> coe du_'215''45'cong_42 v4 v5))
      (\ v0 v1 v2 -> coe du_'215''45'assoc_232)
      (coe du_'215''45'identity_242)
      (coe du_'215''45'distrib'45''8846'_270)
-- Data.Product.Algebra._.⊎-×-isSemiring
d_'8846''45''215''45'isSemiring_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_'8846''45''215''45'isSemiring_288 ~v0
  = du_'8846''45''215''45'isSemiring_288
du_'8846''45''215''45'isSemiring_288 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
du_'8846''45''215''45'isSemiring_288
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_48071
      (coe du_'8846''45''215''45'isSemiringWithoutAnnihilatingZero_286)
      (coe du_'215''45'zero_252)
-- Data.Product.Algebra._.⊎-×-isCommutativeSemiring
d_'8846''45''215''45'isCommutativeSemiring_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'8846''45''215''45'isCommutativeSemiring_290 ~v0
  = du_'8846''45''215''45'isCommutativeSemiring_290
du_'8846''45''215''45'isCommutativeSemiring_290 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
du_'8846''45''215''45'isCommutativeSemiring_290
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51895
      (coe du_'8846''45''215''45'isSemiring_288)
      (\ v0 v1 -> coe du_'215''45'comm_224)
-- Data.Product.Algebra._.×-magma
d_'215''45'magma_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'215''45'magma_292 ~v0 = du_'215''45'magma_292
du_'215''45'magma_292 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_'215''45'magma_292
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1279 erased
      (coe du_'215''45'isMagma_272)
-- Data.Product.Algebra._.×-semigroup
d_'215''45'semigroup_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'215''45'semigroup_294 ~v0 = du_'215''45'semigroup_294
du_'215''45'semigroup_294 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'215''45'semigroup_294
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9793 erased
      (coe du_'215''45'isSemigroup_274)
-- Data.Product.Algebra._.×-monoid
d_'215''45'monoid_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'215''45'monoid_296 ~v0 = du_'215''45'monoid_296
du_'215''45'monoid_296 :: MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'215''45'monoid_296
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16157 erased
      erased (coe du_'215''45'isMonoid_282)
-- Data.Product.Algebra._.×-commutativeMonoid
d_'215''45'commutativeMonoid_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'215''45'commutativeMonoid_298 ~v0
  = du_'215''45'commutativeMonoid_298
du_'215''45'commutativeMonoid_298 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
du_'215''45'commutativeMonoid_298
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17931
      erased erased (coe du_'215''45'isCommutativeMonoid_284)
-- Data.Product.Algebra._.×-⊎-commutativeSemiring
d_'215''45''8846''45'commutativeSemiring_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'215''45''8846''45'commutativeSemiring_300 ~v0
  = du_'215''45''8846''45'commutativeSemiring_300
du_'215''45''8846''45'commutativeSemiring_300 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
du_'215''45''8846''45'commutativeSemiring_300
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_44731
      erased erased erased erased
      (coe du_'8846''45''215''45'isCommutativeSemiring_290)
