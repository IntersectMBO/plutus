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

module MAlonzo.Code.Function.Related.TypeIsomorphisms where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Algebra.Structures.Biased qualified
import MAlonzo.Code.Data.Empty.Polymorphic qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.Product.Function.NonDependent.Propositional qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Data.Sum.Function.Propositional qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Construct.Identity qualified
import MAlonzo.Code.Function.Related.Propositional qualified
import MAlonzo.Code.Level qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Related.TypeIsomorphisms.Σ-assoc
d_Σ'45'assoc_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
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
-- Function.Related.TypeIsomorphisms.×-comm
d_'215''45'comm_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'comm_42 ~v0 ~v1 ~v2 ~v3 = du_'215''45'comm_42
du_'215''45'comm_42 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'comm_42
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Product.Base.du_swap_370)
      (coe MAlonzo.Code.Data.Product.Base.du_swap_370)
-- Function.Related.TypeIsomorphisms.×-identityˡ
d_'215''45'identity'737'_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'identity'737'_50 ~v0 ~v1 = du_'215''45'identity'737'_50
du_'215''45'identity'737'_50 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'identity'737'_50
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Level.C_lift_20
                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
              (coe v0)))
-- Function.Related.TypeIsomorphisms.×-identityʳ
d_'215''45'identity'691'_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'identity'691'_58 ~v0 ~v1 = du_'215''45'identity'691'_58
du_'215''45'identity'691'_58 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'identity'691'_58
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
              (coe
                 MAlonzo.Code.Level.C_lift_20
                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
-- Function.Related.TypeIsomorphisms.×-identity
d_'215''45'identity_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'identity_68 ~v0 = du_'215''45'identity_68
du_'215''45'identity_68 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'identity_68
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'215''45'identity'737'_50)
      (\ v0 -> coe du_'215''45'identity'691'_58)
-- Function.Related.TypeIsomorphisms.×-zeroˡ
d_'215''45'zero'737'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'zero'737'_74 ~v0 ~v1 = du_'215''45'zero'737'_74
du_'215''45'zero'737'_74 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'zero'737'_74
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
         (coe (\ v0 -> v0))
         (\ v0 ->
            coe MAlonzo.Code.Data.Empty.Polymorphic.du_'8869''45'elim_20))
-- Function.Related.TypeIsomorphisms.×-zeroʳ
d_'215''45'zero'691'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'zero'691'_86 ~v0 ~v1 = du_'215''45'zero'691'_86
du_'215''45'zero'691'_86 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'zero'691'_86
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (coe
         MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
         (\ v0 ->
            coe MAlonzo.Code.Data.Empty.Polymorphic.du_'8869''45'elim_20)
         (coe (\ v0 -> v0)))
-- Function.Related.TypeIsomorphisms.×-zero
d_'215''45'zero_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'zero_98 ~v0 = du_'215''45'zero_98
du_'215''45'zero_98 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'zero_98
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'215''45'zero'737'_74)
      (\ v0 -> coe du_'215''45'zero'691'_86)
-- Function.Related.TypeIsomorphisms.⊎-assoc
d_'8846''45'assoc_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'assoc_104 ~v0 ~v1 ~v2 ~v3 = du_'8846''45'assoc_104
du_'8846''45'assoc_104 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'assoc_104
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
         (coe
            MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
            (coe
               MAlonzo.Code.Function.Base.du__'8728''8242'__216
               (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
               (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)))
         (coe
            MAlonzo.Code.Function.Base.du__'8728''8242'__216
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
         (coe
            MAlonzo.Code.Function.Base.du__'8728''8242'__216
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
         (coe
            MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
            (coe
               MAlonzo.Code.Function.Base.du__'8728''8242'__216
               (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
               (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42))
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)))
-- Function.Related.TypeIsomorphisms.⊎-comm
d_'8846''45'comm_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'comm_124 ~v0 ~v1 ~v2 ~v3 = du_'8846''45'comm_124
du_'8846''45'comm_124 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'comm_124
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Sum.Base.du_swap_78)
      (coe MAlonzo.Code.Data.Sum.Base.du_swap_78)
-- Function.Related.TypeIsomorphisms.⊎-identityˡ
d_'8846''45'identity'737'_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'identity'737'_128 ~v0 ~v1
  = du_'8846''45'identity'737'_128
du_'8846''45'identity'737'_128 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'identity'737'_128
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 erased
         (\ v0 -> v0))
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
-- Function.Related.TypeIsomorphisms.⊎-identityʳ
d_'8846''45'identity'691'_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8846''45'identity'691'_136 ~v0 ~v1
  = du_'8846''45'identity'691'_136
du_'8846''45'identity'691'_136 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8846''45'identity'691'_136
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 (\ v0 -> v0)
         erased)
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
-- Function.Related.TypeIsomorphisms.⊎-identity
d_'8846''45'identity_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8846''45'identity_144 ~v0 = du_'8846''45'identity_144
du_'8846''45'identity_144 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8846''45'identity_144
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'8846''45'identity'737'_128)
      (\ v0 -> coe du_'8846''45'identity'691'_136)
-- Function.Related.TypeIsomorphisms.×-distribˡ-⊎
d_'215''45'distrib'737''45''8846'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'distrib'737''45''8846'_150 ~v0 ~v1 ~v2 ~v3
  = du_'215''45'distrib'737''45''8846'_150
du_'215''45'distrib'737''45''8846'_150 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'distrib'737''45''8846'_150
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
-- Function.Related.TypeIsomorphisms.×-distribʳ-⊎
d_'215''45'distrib'691''45''8846'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'215''45'distrib'691''45''8846'_172 ~v0 ~v1 ~v2 ~v3
  = du_'215''45'distrib'691''45''8846'_172
du_'215''45'distrib'691''45''8846'_172 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'215''45'distrib'691''45''8846'_172
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
-- Function.Related.TypeIsomorphisms.×-distrib-⊎
d_'215''45'distrib'45''8846'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'distrib'45''8846'_190 ~v0
  = du_'215''45'distrib'45''8846'_190
du_'215''45'distrib'45''8846'_190 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'distrib'45''8846'_190
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 -> coe du_'215''45'distrib'737''45''8846'_150)
      (\ v0 v1 v2 -> coe du_'215''45'distrib'691''45''8846'_172)
-- Function.Related.TypeIsomorphisms.×-isMagma
d_'215''45'isMagma_198 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'215''45'isMagma_198 v0 ~v1 = du_'215''45'isMagma_198 v0
du_'215''45'isMagma_198 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'215''45'isMagma_198 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Function.Related.Propositional.du_SK'45'isEquivalence_172
         (coe v0))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Data.Product.Function.NonDependent.Propositional.du__'215''45'cong__96
              (coe
                 MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                 (coe v0))))
-- Function.Related.TypeIsomorphisms.×-magma
d_'215''45'magma_206 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'215''45'magma_206 v0 ~v1 = du_'215''45'magma_206 v0
du_'215''45'magma_206 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_'215''45'magma_206 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1279 erased
      (coe du_'215''45'isMagma_198 (coe v0))
-- Function.Related.TypeIsomorphisms.×-isSemigroup
d_'215''45'isSemigroup_216 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'215''45'isSemigroup_216 v0 ~v1 = du_'215''45'isSemigroup_216 v0
du_'215''45'isSemigroup_216 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'215''45'isSemigroup_216 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe du_'215''45'isMagma_198 (coe v0))
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
              (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                 (coe v0))
              (coe du_Σ'45'assoc_32)))
-- Function.Related.TypeIsomorphisms.×-semigroup
d_'215''45'semigroup_230 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'215''45'semigroup_230 v0 ~v1 = du_'215''45'semigroup_230 v0
du_'215''45'semigroup_230 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'215''45'semigroup_230 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9793 erased
      (coe du_'215''45'isSemigroup_216 (coe v0))
-- Function.Related.TypeIsomorphisms.×-isMonoid
d_'215''45'isMonoid_240 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'215''45'isMonoid_240 v0 ~v1 = du_'215''45'isMonoid_240 v0
du_'215''45'isMonoid_240 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'215''45'isMonoid_240 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe du_'215''45'isSemigroup_216 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
                 (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                    (coe v0))
                 (coe du_'215''45'identity'737'_50)))
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
                 (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                    (coe v0))
                 (coe du_'215''45'identity'691'_58))))
-- Function.Related.TypeIsomorphisms.×-monoid
d_'215''45'monoid_248 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'215''45'monoid_248 v0 ~v1 = du_'215''45'monoid_248 v0
du_'215''45'monoid_248 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'215''45'monoid_248 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16157 erased
      erased (coe du_'215''45'isMonoid_240 (coe v0))
-- Function.Related.TypeIsomorphisms.×-isCommutativeMonoid
d_'215''45'isCommutativeMonoid_258 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'215''45'isCommutativeMonoid_258 v0 ~v1
  = du_'215''45'isCommutativeMonoid_258 v0
du_'215''45'isCommutativeMonoid_258 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_'215''45'isCommutativeMonoid_258 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe du_'215''45'isMonoid_240 (coe v0))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
              (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                 (coe v0))
              (coe du_'215''45'comm_42)))
-- Function.Related.TypeIsomorphisms.×-commutativeMonoid
d_'215''45'commutativeMonoid_270 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'215''45'commutativeMonoid_270 v0 ~v1
  = du_'215''45'commutativeMonoid_270 v0
du_'215''45'commutativeMonoid_270 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
du_'215''45'commutativeMonoid_270 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17931
      erased erased (coe du_'215''45'isCommutativeMonoid_258 (coe v0))
-- Function.Related.TypeIsomorphisms.⊎-isMagma
d_'8846''45'isMagma_280 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8846''45'isMagma_280 v0 ~v1 = du_'8846''45'isMagma_280 v0
du_'8846''45'isMagma_280 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8846''45'isMagma_280 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Function.Related.Propositional.du_SK'45'isEquivalence_172
         (coe v0))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Data.Sum.Function.Propositional.du__'8846''45'cong__94
              (coe
                 MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                 (coe v0))))
-- Function.Related.TypeIsomorphisms.⊎-magma
d_'8846''45'magma_288 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8846''45'magma_288 v0 ~v1 = du_'8846''45'magma_288 v0
du_'8846''45'magma_288 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_'8846''45'magma_288 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1279 erased
      (coe du_'8846''45'isMagma_280 (coe v0))
-- Function.Related.TypeIsomorphisms.⊎-isSemigroup
d_'8846''45'isSemigroup_298 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8846''45'isSemigroup_298 v0 ~v1
  = du_'8846''45'isSemigroup_298 v0
du_'8846''45'isSemigroup_298 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8846''45'isSemigroup_298 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe du_'8846''45'isMagma_280 (coe v0))
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
              (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                 (coe v0))
              (coe du_'8846''45'assoc_104)))
-- Function.Related.TypeIsomorphisms.⊎-semigroup
d_'8846''45'semigroup_312 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8846''45'semigroup_312 v0 ~v1 = du_'8846''45'semigroup_312 v0
du_'8846''45'semigroup_312 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'8846''45'semigroup_312 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9793 erased
      (coe du_'8846''45'isSemigroup_298 (coe v0))
-- Function.Related.TypeIsomorphisms.⊎-isMonoid
d_'8846''45'isMonoid_322 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8846''45'isMonoid_322 v0 ~v1 = du_'8846''45'isMonoid_322 v0
du_'8846''45'isMonoid_322 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'8846''45'isMonoid_322 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe du_'8846''45'isSemigroup_298 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
                 (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                    (coe v0))
                 (coe du_'8846''45'identity'737'_128)))
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
                 (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                    (coe v0))
                 (coe du_'8846''45'identity'691'_136))))
-- Function.Related.TypeIsomorphisms.⊎-monoid
d_'8846''45'monoid_330 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'8846''45'monoid_330 v0 ~v1 = du_'8846''45'monoid_330 v0
du_'8846''45'monoid_330 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'8846''45'monoid_330 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16157 erased
      erased (coe du_'8846''45'isMonoid_322 (coe v0))
-- Function.Related.TypeIsomorphisms.⊎-isCommutativeMonoid
d_'8846''45'isCommutativeMonoid_340 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'8846''45'isCommutativeMonoid_340 v0 ~v1
  = du_'8846''45'isCommutativeMonoid_340 v0
du_'8846''45'isCommutativeMonoid_340 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
du_'8846''45'isCommutativeMonoid_340 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17695
      (coe du_'8846''45'isMonoid_322 (coe v0))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
              (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                 (coe v0))
              (coe du_'8846''45'comm_124)))
-- Function.Related.TypeIsomorphisms.⊎-commutativeMonoid
d_'8846''45'commutativeMonoid_352 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'8846''45'commutativeMonoid_352 v0 ~v1
  = du_'8846''45'commutativeMonoid_352 v0
du_'8846''45'commutativeMonoid_352 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
du_'8846''45'commutativeMonoid_352 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17931
      erased erased (coe du_'8846''45'isCommutativeMonoid_340 (coe v0))
-- Function.Related.TypeIsomorphisms.×-⊎-isCommutativeSemiring
d_'215''45''8846''45'isCommutativeSemiring_362 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'215''45''8846''45'isCommutativeSemiring_362 v0 ~v1
  = du_'215''45''8846''45'isCommutativeSemiring_362 v0
du_'215''45''8846''45'isCommutativeSemiring_362 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
du_'215''45''8846''45'isCommutativeSemiring_362 v0
  = coe
      MAlonzo.Code.Algebra.Structures.Biased.du_isCommutativeSemiring_2996
      erased erased erased
      (coe
         MAlonzo.Code.Algebra.Structures.Biased.C_IsCommutativeSemiring'737''46'constructor_43731
         (coe du_'8846''45'isCommutativeMonoid_340 (coe v0))
         (coe du_'215''45'isCommutativeMonoid_258 (coe v0))
         (coe
            (\ v1 v2 v3 ->
               coe
                 MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
                 (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                    (coe v0))
                 (coe du_'215''45'distrib'691''45''8846'_172)))
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
                 (MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                    (coe v0))
                 (coe du_'215''45'zero'737'_74))))
-- Function.Related.TypeIsomorphisms.×-⊎-commutativeSemiring
d_'215''45''8846''45'commutativeSemiring_376 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'215''45''8846''45'commutativeSemiring_376 v0 ~v1
  = du_'215''45''8846''45'commutativeSemiring_376 v0
du_'215''45''8846''45'commutativeSemiring_376 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
du_'215''45''8846''45'commutativeSemiring_376 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_44731
      erased erased erased erased
      (coe du_'215''45''8846''45'isCommutativeSemiring_362 (coe v0))
-- Function.Related.TypeIsomorphisms.ΠΠ↔ΠΠ
d_ΠΠ'8596'ΠΠ_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_ΠΠ'8596'ΠΠ_402 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_ΠΠ'8596'ΠΠ_402
du_ΠΠ'8596'ΠΠ_402 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_ΠΠ'8596'ΠΠ_402
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 v1 v2 -> coe v0 v2 v1))
      (coe (\ v0 v1 v2 -> coe v0 v2 v1))
-- Function.Related.TypeIsomorphisms.∃∃↔∃∃
d_'8707''8707''8596''8707''8707'_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8707''8707''8596''8707''8707'_428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8707''8707''8596''8707''8707'_428
du_'8707''8707''8596''8707''8707'_428 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8707''8707''8596''8707''8707'_428
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe du_to_444) (coe du_from_460)
-- Function.Related.TypeIsomorphisms._.to
d_to_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_to_444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_to_444 v6
du_to_444 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_to_444 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Related.TypeIsomorphisms._.from
d_from_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from_460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_from_460 v6
du_from_460 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_from_460 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Related.TypeIsomorphisms.Π↔Π
d_Π'8596'Π_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_Π'8596'Π_480 ~v0 ~v1 ~v2 ~v3 = du_Π'8596'Π_480
du_Π'8596'Π_480 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_Π'8596'Π_480
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 v1 -> coe v0 v1)) (coe (\ v0 v1 -> coe v0 v1))
-- Function.Related.TypeIsomorphisms.→-cong-⇔
d_'8594''45'cong'45''8660'_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8594''45'cong'45''8660'_486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                               v9
  = du_'8594''45'cong'45''8660'_486 v8 v9
du_'8594''45'cong'45''8660'_486 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8594''45'cong'45''8660'_486 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1724 v1
              (coe v2 (coe MAlonzo.Code.Function.Bundles.d_from_1726 v0 v3))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1726 v1
              (coe v2 (coe MAlonzo.Code.Function.Bundles.d_to_1724 v0 v3))))
-- Function.Related.TypeIsomorphisms.→-cong-↔
d_'8594''45'cong'45''8596'_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8594''45'cong'45''8596'_508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10 v11
  = du_'8594''45'cong'45''8596'_508 v10 v11
du_'8594''45'cong'45''8596'_508 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8594''45'cong'45''8596'_508 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1972 v1
              (coe v2 (coe MAlonzo.Code.Function.Bundles.d_from_1974 v0 v3))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1974 v1
              (coe v2 (coe MAlonzo.Code.Function.Bundles.d_to_1972 v0 v3))))
-- Function.Related.TypeIsomorphisms.→-cong
d_'8594''45'cong_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  () -> () -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_'8594''45'cong_544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_'8594''45'cong_544 v6
du_'8594''45'cong_544 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8594''45'cong_544 v0
  = case coe v0 of
      MAlonzo.Code.Function.Related.Propositional.C_equivalence_88
        -> coe du_'8594''45'cong'45''8660'_486
      MAlonzo.Code.Function.Related.Propositional.C_bijection_90
        -> coe du_'8594''45'cong'45''8596'_508
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Related.TypeIsomorphisms.¬-cong-⇔
d_'172''45'cong'45''8660'_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'172''45'cong'45''8660'_554 ~v0 ~v1 ~v2 ~v3 v4
  = du_'172''45'cong'45''8660'_554 v4
du_'172''45'cong'45''8660'_554 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'172''45'cong'45''8660'_554 v0
  = coe
      du_'8594''45'cong'45''8660'_486 (coe v0)
      (coe MAlonzo.Code.Function.Construct.Identity.du_'8660''45'id_814)
-- Function.Related.TypeIsomorphisms.¬-cong
d_'172''45'cong_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  () -> () -> AgdaAny -> AgdaAny
d_'172''45'cong_564 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_'172''45'cong_564 v4 v7
du_'172''45'cong_564 ::
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  AgdaAny -> AgdaAny
du_'172''45'cong_564 v0 v1
  = coe
      du_'8594''45'cong_544 v0 v1
      (coe
         MAlonzo.Code.Function.Related.Propositional.du_K'45'reflexive_162
         (coe
            MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
            (coe v0)))
-- Function.Related.TypeIsomorphisms.Related-cong
d_Related'45'cong_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_Related'45'cong_574 ~v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9 v10
  = du_Related'45'cong_574 v1 v3 v5 v7 v8 v9 v10
du_Related'45'cong_574 ::
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Function.Related.Propositional.T_SymmetricKind_86 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_Related'45'cong_574 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
      (coe
         (\ v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
              (\ v8 v9 v10 ->
                 coe
                   MAlonzo.Code.Function.Related.Propositional.du_K'45'trans_164
                   (coe
                      MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                      (coe v4)))
              v1 v0 v3
              (coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
                 (\ v8 v9 v10 ->
                    coe
                      MAlonzo.Code.Function.Related.Propositional.du_K'45'trans_164
                      (coe
                         MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                         (coe v4)))
                 v0 v2 v3
                 (coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
                    (\ v8 v9 v10 ->
                       coe
                         MAlonzo.Code.Function.Related.Propositional.du_K'45'trans_164
                         (coe
                            MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                            (coe v4)))
                    v2 v3 v3
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                       (\ v8 ->
                          coe
                            MAlonzo.Code.Function.Related.Propositional.du_K'45'refl_160
                            (coe
                               MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                               (coe v4)))
                       (coe v3))
                    v6)
                 v7)
              (coe
                 MAlonzo.Code.Function.Related.Propositional.du_SK'45'sym_168 v4
                 v5)))
      (coe
         (\ v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
              (\ v8 v9 v10 ->
                 coe
                   MAlonzo.Code.Function.Related.Propositional.du_K'45'trans_164
                   (coe
                      MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                      (coe v4)))
              v0 v1 v2
              (coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
                 (\ v8 v9 v10 ->
                    coe
                      MAlonzo.Code.Function.Related.Propositional.du_K'45'trans_164
                      (coe
                         MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                         (coe v4)))
                 v1 v3 v2
                 (coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
                    (\ v8 v9 v10 ->
                       coe
                         MAlonzo.Code.Function.Related.Propositional.du_K'45'trans_164
                         (coe
                            MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                            (coe v4)))
                    v3 v2 v2
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                       (\ v8 ->
                          coe
                            MAlonzo.Code.Function.Related.Propositional.du_K'45'refl_160
                            (coe
                               MAlonzo.Code.Function.Related.Propositional.d_'8970'_'8971'_92
                               (coe v4)))
                       (coe v2))
                    (coe
                       MAlonzo.Code.Function.Related.Propositional.du_SK'45'sym_168 v4
                       v6))
                 v7)
              v5))
-- Function.Related.TypeIsomorphisms.True↔
d_True'8596'_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_True'8596'_606 ~v0 ~v1 v2 ~v3 = du_True'8596'_606 v2
du_True'8596'_606 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_True'8596'_606 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
                    (coe
                       (\ v3 ->
                          coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2)))
                    (coe (\ v3 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366 erased
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
      _ -> MAlonzo.RTE.mazUnreachableError
