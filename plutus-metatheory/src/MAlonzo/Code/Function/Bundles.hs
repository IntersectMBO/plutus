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

module MAlonzo.Code.Function.Bundles where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Consequences.Propositional qualified
import MAlonzo.Code.Function.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Bundles._._._≈_
d__'8776'__30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__30 = erased
-- Function.Bundles._._.Carrier
d_Carrier_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 -> ()
d_Carrier_32 = erased
-- Function.Bundles._._.IsBijection
d_IsBijection_46 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsCongruent
d_IsCongruent_48 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsInjection
d_IsInjection_50 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsSurjection
d_IsSurjection_60 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsBijection.isInjection
d_isInjection_204 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
d_isInjection_204 v0
  = coe MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0)
-- Function.Bundles._._.IsBijection.surjective
d_surjective_210 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_210 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_248 (coe v0)
-- Function.Bundles._._.IsBijection.Eq₁._≈_
d__'8776'__214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__214 = erased
-- Function.Bundles._._.IsBijection.Eq₁._≉_
d__'8777'__216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__216 = erased
-- Function.Bundles._._.IsBijection.Eq₁.Carrier
d_Carrier_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 -> ()
d_Carrier_218 = erased
-- Function.Bundles._._.IsBijection.Eq₁.isEquivalence
d_isEquivalence_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_220 v7
du_isEquivalence_220 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_220 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v2)))
-- Function.Bundles._._.IsBijection.Eq₁.isPartialEquivalence
d_isPartialEquivalence_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_222 v7
du_isPartialEquivalence_222 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_222 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₁.partialSetoid
d_partialSetoid_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_224 v7
du_partialSetoid_224 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_224 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2))))
-- Function.Bundles._._.IsBijection.Eq₁.refl
d_refl_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny
d_refl_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_226 v7
du_refl_226 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny
du_refl_226 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v2))))
-- Function.Bundles._._.IsBijection.Eq₁.reflexive
d_reflexive_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_228 v7
du_reflexive_228 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_228 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Bundles._._.IsBijection.Eq₁.setoid
d_setoid_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_230 v7
du_setoid_230 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_230 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1)))
-- Function.Bundles._._.IsBijection.Eq₁.sym
d_sym_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_232 v7
du_sym_232 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_232 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₁.trans
d_trans_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_234 v7
du_trans_234 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_234 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₂._≈_
d__'8776'__238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__238 = erased
-- Function.Bundles._._.IsBijection.Eq₂._≉_
d__'8777'__240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__240 = erased
-- Function.Bundles._._.IsBijection.Eq₂.Carrier
d_Carrier_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 -> ()
d_Carrier_242 = erased
-- Function.Bundles._._.IsBijection.Eq₂.isEquivalence
d_isEquivalence_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_244 v7
du_isEquivalence_244 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_244 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v2)))
-- Function.Bundles._._.IsBijection.Eq₂.isPartialEquivalence
d_isPartialEquivalence_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_246 v7
du_isPartialEquivalence_246 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_246 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₂.partialSetoid
d_partialSetoid_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_248 v7
du_partialSetoid_248 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_248 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2))))
-- Function.Bundles._._.IsBijection.Eq₂.refl
d_refl_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny
d_refl_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_250 v7
du_refl_250 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny
du_refl_250 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v2))))
-- Function.Bundles._._.IsBijection.Eq₂.reflexive
d_reflexive_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_252 v7
du_reflexive_252 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_252 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Bundles._._.IsBijection.Eq₂.setoid
d_setoid_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_254 v7
du_setoid_254 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_254 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_66
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1)))
-- Function.Bundles._._.IsBijection.Eq₂.sym
d_sym_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_256 v7
du_sym_256 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_256 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₂.trans
d_trans_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_258 v7
du_trans_258 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_258 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsCongruent.cong
d_cong_262 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_262 v0
  = coe MAlonzo.Code.Function.Structures.d_cong_32 (coe v0)
-- Function.Bundles._._.IsCongruent.isEquivalence₁
d_isEquivalence'8321'_264 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_264 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Bundles._._.IsCongruent.isEquivalence₂
d_isEquivalence'8322'_266 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_266 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Bundles._._.IsCongruent.Eq₁._≈_
d__'8776'__270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__270 = erased
-- Function.Bundles._._.IsCongruent.Eq₁._≉_
d__'8777'__272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__272 = erased
-- Function.Bundles._._.IsCongruent.Eq₁.Carrier
d_Carrier_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 -> ()
d_Carrier_274 = erased
-- Function.Bundles._._.IsCongruent.Eq₁.isEquivalence
d_isEquivalence_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_276 v7
du_isEquivalence_276 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_276 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Bundles._._.IsCongruent.Eq₁.isPartialEquivalence
d_isPartialEquivalence_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_278 v7
du_isPartialEquivalence_278 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_278 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₁.partialSetoid
d_partialSetoid_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_280 v7
du_partialSetoid_280 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_280 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
      (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0))
-- Function.Bundles._._.IsCongruent.Eq₁.refl
d_refl_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
d_refl_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_282 v7
du_refl_282 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
du_refl_282 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0))
-- Function.Bundles._._.IsCongruent.Eq₁.reflexive
d_reflexive_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_284 v7
du_reflexive_284 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_284 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
           v2)
-- Function.Bundles._._.IsCongruent.Eq₁.setoid
d_setoid_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_setoid_286
du_setoid_286 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_286 v0 v1
  = coe MAlonzo.Code.Function.Structures.du_setoid_40 v1
-- Function.Bundles._._.IsCongruent.Eq₁.sym
d_sym_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_288 v7
du_sym_288 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_288 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₁.trans
d_trans_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_290 v7
du_trans_290 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_290 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₂._≈_
d__'8776'__294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__294 = erased
-- Function.Bundles._._.IsCongruent.Eq₂._≉_
d__'8777'__296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__296 = erased
-- Function.Bundles._._.IsCongruent.Eq₂.Carrier
d_Carrier_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 -> ()
d_Carrier_298 = erased
-- Function.Bundles._._.IsCongruent.Eq₂.isEquivalence
d_isEquivalence_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_300 v7
du_isEquivalence_300 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_300 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Bundles._._.IsCongruent.Eq₂.isPartialEquivalence
d_isPartialEquivalence_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_302 v7
du_isPartialEquivalence_302 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_302 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₂.partialSetoid
d_partialSetoid_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_304 v7
du_partialSetoid_304 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
      (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0))
-- Function.Bundles._._.IsCongruent.Eq₂.refl
d_refl_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
d_refl_306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_306 v7
du_refl_306 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
du_refl_306 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0))
-- Function.Bundles._._.IsCongruent.Eq₂.reflexive
d_reflexive_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_308 v7
du_reflexive_308 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_308 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
           v2)
-- Function.Bundles._._.IsCongruent.Eq₂.setoid
d_setoid_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_setoid_310
du_setoid_310 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_310 v0 v1
  = coe MAlonzo.Code.Function.Structures.du_setoid_66 v1
-- Function.Bundles._._.IsCongruent.Eq₂.sym
d_sym_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_312 v7
du_sym_312 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_312 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₂.trans
d_trans_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_314 v7
du_trans_314 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_314 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Bundles._._.IsInjection.injective
d_injective_320 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_320 v0
  = coe MAlonzo.Code.Function.Structures.d_injective_102 (coe v0)
-- Function.Bundles._._.IsInjection.isCongruent
d_isCongruent_322 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_322 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v0)
-- Function.Bundles._._.IsSurjection.isCongruent
d_isCongruent_656 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_656 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_170 (coe v0)
-- Function.Bundles._._.IsSurjection.strictlySurjective
d_strictlySurjective_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_strictlySurjective_662
du_strictlySurjective_662 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective_662 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlySurjective_230 v1 v2
-- Function.Bundles._._.IsSurjection.surjective
d_surjective_664 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_664 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_172 (coe v0)
-- Function.Bundles._.Func
d_Func_714 a0 a1 a2 a3 a4 a5 = ()
data T_Func_714
  = C_Func'46'constructor_6307 (AgdaAny -> AgdaAny)
                               (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.Func.to
d_to_720 :: T_Func_714 -> AgdaAny -> AgdaAny
d_to_720 v0
  = case coe v0 of
      C_Func'46'constructor_6307 v1 v2 -> coe v1
      _                                -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Func.cong
d_cong_722 ::
  T_Func_714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_722 v0
  = case coe v0 of
      C_Func'46'constructor_6307 v1 v2 -> coe v2
      _                                -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Func.isCongruent
d_isCongruent_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_724 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_724 v4 v5 v6
du_isCongruent_724 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_724 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsCongruent'46'constructor_985
      (coe d_cong_722 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
-- Function.Bundles._.Func._.Eq₁._≈_
d__'8776'__730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny -> ()
d__'8776'__730 = erased
-- Function.Bundles._.Func._.Eq₁._≉_
d__'8777'__732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny -> ()
d__'8777'__732 = erased
-- Function.Bundles._.Func._.Eq₁.Carrier
d_Carrier_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> ()
d_Carrier_734 = erased
-- Function.Bundles._.Func._.Eq₁.isEquivalence
d_isEquivalence_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_736 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_736 v4 v5 v6
du_isEquivalence_736 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_736 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v3))
-- Function.Bundles._.Func._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_738 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_738 v4 v5 v6
du_isPartialEquivalence_738 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_738 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v4))))
-- Function.Bundles._.Func._.Eq₁.partialSetoid
d_partialSetoid_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_740 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_740 v4 v5 v6
du_partialSetoid_740 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_740 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3)))
-- Function.Bundles._.Func._.Eq₁.refl
d_refl_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny
d_refl_742 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_742 v4 v5 v6
du_refl_742 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny
du_refl_742 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v3)))
-- Function.Bundles._.Func._.Eq₁.reflexive
d_reflexive_744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_744 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_744 v4 v5 v6
du_reflexive_744 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_744 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3) in
       coe
         (\ v5 v6 v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v4))
              v5))
-- Function.Bundles._.Func._.Eq₁.setoid
d_setoid_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_746 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_746 v4 v5 v6
du_setoid_746 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_746 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe du_isCongruent_724 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.Func._.Eq₁.sym
d_sym_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_748 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_748 v4 v5 v6
du_sym_748 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_748 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v4))))
-- Function.Bundles._.Func._.Eq₁.trans
d_trans_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_750 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_750 v4 v5 v6
du_trans_750 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_750 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v4))))
-- Function.Bundles._.Func._.Eq₂._≈_
d__'8776'__754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny -> ()
d__'8776'__754 = erased
-- Function.Bundles._.Func._.Eq₂._≉_
d__'8777'__756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny -> ()
d__'8777'__756 = erased
-- Function.Bundles._.Func._.Eq₂.Carrier
d_Carrier_758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> ()
d_Carrier_758 = erased
-- Function.Bundles._.Func._.Eq₂.isEquivalence
d_isEquivalence_760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_760 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_760 v4 v5 v6
du_isEquivalence_760 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_760 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v3))
-- Function.Bundles._.Func._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_762 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_762 v4 v5 v6
du_isPartialEquivalence_762 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_762 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v4))))
-- Function.Bundles._.Func._.Eq₂.partialSetoid
d_partialSetoid_764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_764 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_764 v4 v5 v6
du_partialSetoid_764 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_764 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v3)))
-- Function.Bundles._.Func._.Eq₂.refl
d_refl_766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny
d_refl_766 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_766 v4 v5 v6
du_refl_766 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny
du_refl_766 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v3)))
-- Function.Bundles._.Func._.Eq₂.reflexive
d_reflexive_768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_768 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_768 v4 v5 v6
du_reflexive_768 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_768 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v3) in
       coe
         (\ v5 v6 v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v4))
              v5))
-- Function.Bundles._.Func._.Eq₂.setoid
d_setoid_770 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_770 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_770 v4 v5 v6
du_setoid_770 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_770 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_66
      (coe du_isCongruent_724 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.Func._.Eq₂.sym
d_sym_772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_772 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_772 v4 v5 v6
du_sym_772 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_772 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v4))))
-- Function.Bundles._.Func._.Eq₂.trans
d_trans_774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_774 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_774 v4 v5 v6
du_trans_774 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Func_714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_774 v0 v1 v2
  = let v3 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v4))))
-- Function.Bundles._.Injection
d_Injection_776 a0 a1 a2 a3 a4 a5 = ()
data T_Injection_776
  = C_Injection'46'constructor_8675 (AgdaAny -> AgdaAny)
                                    (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                    (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.Injection.to
d_to_784 :: T_Injection_776 -> AgdaAny -> AgdaAny
d_to_784 v0
  = case coe v0 of
      C_Injection'46'constructor_8675 v1 v2 v3 -> coe v1
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Injection.cong
d_cong_786 ::
  T_Injection_776 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_786 v0
  = case coe v0 of
      C_Injection'46'constructor_8675 v1 v2 v3 -> coe v2
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Injection.injective
d_injective_788 ::
  T_Injection_776 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_788 v0
  = case coe v0 of
      C_Injection'46'constructor_8675 v1 v2 v3 -> coe v3
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Injection.function
d_function_790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> T_Func_714
d_function_790 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_function_790 v6
du_function_790 :: T_Injection_776 -> T_Func_714
du_function_790 v0
  = coe
      C_Func'46'constructor_6307 (coe d_to_784 (coe v0))
      (coe d_cong_786 (coe v0))
-- Function.Bundles._.Injection._.isCongruent
d_isCongruent_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_794 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_794 v4 v5 v6
du_isCongruent_794 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_794 v0 v1 v2
  = coe
      du_isCongruent_724 (coe v0) (coe v1) (coe du_function_790 (coe v2))
-- Function.Bundles._.Injection._.Eq₁._≈_
d__'8776'__798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny -> ()
d__'8776'__798 = erased
-- Function.Bundles._.Injection._.Eq₁._≉_
d__'8777'__800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny -> ()
d__'8777'__800 = erased
-- Function.Bundles._.Injection._.Eq₁.Carrier
d_Carrier_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> ()
d_Carrier_802 = erased
-- Function.Bundles._.Injection._.Eq₁.isEquivalence
d_isEquivalence_804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_804 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_804 v4 v5 v6
du_isEquivalence_804 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_804 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.Injection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_806 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_806 v4 v5 v6
du_isPartialEquivalence_806 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_806 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₁.partialSetoid
d_partialSetoid_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_808 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_808 v4 v5 v6
du_partialSetoid_808 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_808 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.Injection._.Eq₁.refl
d_refl_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny
d_refl_810 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_810 v4 v5 v6
du_refl_810 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny
du_refl_810 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.Injection._.Eq₁.reflexive
d_reflexive_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_812 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_812 v4 v5 v6
du_reflexive_812 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_812 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.Injection._.Eq₁.setoid
d_setoid_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_814 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_814 v4 v5 v6
du_setoid_814 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_814 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe du_isCongruent_724 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Injection._.Eq₁.sym
d_sym_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_816 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_816 v4 v5 v6
du_sym_816 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_816 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₁.trans
d_trans_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_818 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_818 v4 v5 v6
du_trans_818 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_818 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₂._≈_
d__'8776'__822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny -> ()
d__'8776'__822 = erased
-- Function.Bundles._.Injection._.Eq₂._≉_
d__'8777'__824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny -> ()
d__'8777'__824 = erased
-- Function.Bundles._.Injection._.Eq₂.Carrier
d_Carrier_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> ()
d_Carrier_826 = erased
-- Function.Bundles._.Injection._.Eq₂.isEquivalence
d_isEquivalence_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_828 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_828 v4 v5 v6
du_isEquivalence_828 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_828 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.Injection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_830 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_830 v4 v5 v6
du_isPartialEquivalence_830 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_830 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₂.partialSetoid
d_partialSetoid_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_832 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_832 v4 v5 v6
du_partialSetoid_832 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_832 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4))))
-- Function.Bundles._.Injection._.Eq₂.refl
d_refl_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny
d_refl_834 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_834 v4 v5 v6
du_refl_834 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny
du_refl_834 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.Injection._.Eq₂.reflexive
d_reflexive_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_836 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_836 v4 v5 v6
du_reflexive_836 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_836 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.Injection._.Eq₂.setoid
d_setoid_838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_838 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_838 v4 v5 v6
du_setoid_838 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_838 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_66
         (coe du_isCongruent_724 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Injection._.Eq₂.sym
d_sym_840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_840 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_840 v4 v5 v6
du_sym_840 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_840 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₂.trans
d_trans_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_842 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_842 v4 v5 v6
du_trans_842 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_842 v0 v1 v2
  = let v3 = coe du_function_790 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Injection.isInjection
d_isInjection_844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
d_isInjection_844 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isInjection_844 v4 v5 v6
du_isInjection_844 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Injection_776 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
du_isInjection_844 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsInjection'46'constructor_3997
      (coe
         du_isCongruent_724 (coe v0) (coe v1)
         (coe du_function_790 (coe v2)))
      (coe d_injective_788 (coe v2))
-- Function.Bundles._.Surjection
d_Surjection_846 a0 a1 a2 a3 a4 a5 = ()
data T_Surjection_846
  = C_Surjection'46'constructor_11197 (AgdaAny -> AgdaAny)
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                      (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Function.Bundles._.Surjection.to
d_to_854 :: T_Surjection_846 -> AgdaAny -> AgdaAny
d_to_854 v0
  = case coe v0 of
      C_Surjection'46'constructor_11197 v1 v2 v3 -> coe v1
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Surjection.cong
d_cong_856 ::
  T_Surjection_846 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_856 v0
  = case coe v0 of
      C_Surjection'46'constructor_11197 v1 v2 v3 -> coe v2
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Surjection.surjective
d_surjective_858 ::
  T_Surjection_846 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_858 v0
  = case coe v0 of
      C_Surjection'46'constructor_11197 v1 v2 v3 -> coe v3
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Surjection.function
d_function_860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> T_Func_714
d_function_860 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_function_860 v6
du_function_860 :: T_Surjection_846 -> T_Func_714
du_function_860 v0
  = coe
      C_Func'46'constructor_6307 (coe d_to_854 (coe v0))
      (coe d_cong_856 (coe v0))
-- Function.Bundles._.Surjection._.isCongruent
d_isCongruent_864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_864 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_864 v4 v5 v6
du_isCongruent_864 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_864 v0 v1 v2
  = coe
      du_isCongruent_724 (coe v0) (coe v1) (coe du_function_860 (coe v2))
-- Function.Bundles._.Surjection._.Eq₁._≈_
d__'8776'__868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny -> ()
d__'8776'__868 = erased
-- Function.Bundles._.Surjection._.Eq₁._≉_
d__'8777'__870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny -> ()
d__'8777'__870 = erased
-- Function.Bundles._.Surjection._.Eq₁.Carrier
d_Carrier_872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> ()
d_Carrier_872 = erased
-- Function.Bundles._.Surjection._.Eq₁.isEquivalence
d_isEquivalence_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_874 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_874 v4 v5 v6
du_isEquivalence_874 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_874 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.Surjection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_876 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_876 v4 v5 v6
du_isPartialEquivalence_876 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_876 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₁.partialSetoid
d_partialSetoid_878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_878 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_878 v4 v5 v6
du_partialSetoid_878 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_878 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.Surjection._.Eq₁.refl
d_refl_880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny
d_refl_880 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_880 v4 v5 v6
du_refl_880 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny
du_refl_880 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.Surjection._.Eq₁.reflexive
d_reflexive_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_882 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_882 v4 v5 v6
du_reflexive_882 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_882 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.Surjection._.Eq₁.setoid
d_setoid_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_884 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_884 v4 v5 v6
du_setoid_884 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_884 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe du_isCongruent_724 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Surjection._.Eq₁.sym
d_sym_886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_886 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_886 v4 v5 v6
du_sym_886 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_886 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₁.trans
d_trans_888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_888 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_888 v4 v5 v6
du_trans_888 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_888 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₂._≈_
d__'8776'__892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny -> ()
d__'8776'__892 = erased
-- Function.Bundles._.Surjection._.Eq₂._≉_
d__'8777'__894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny -> ()
d__'8777'__894 = erased
-- Function.Bundles._.Surjection._.Eq₂.Carrier
d_Carrier_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> ()
d_Carrier_896 = erased
-- Function.Bundles._.Surjection._.Eq₂.isEquivalence
d_isEquivalence_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_898 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_898 v4 v5 v6
du_isEquivalence_898 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_898 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.Surjection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_900 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_900 v4 v5 v6
du_isPartialEquivalence_900 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_900 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₂.partialSetoid
d_partialSetoid_902 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_902 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_902 v4 v5 v6
du_partialSetoid_902 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_902 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4))))
-- Function.Bundles._.Surjection._.Eq₂.refl
d_refl_904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny
d_refl_904 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_904 v4 v5 v6
du_refl_904 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny
du_refl_904 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.Surjection._.Eq₂.reflexive
d_reflexive_906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_906 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_906 v4 v5 v6
du_reflexive_906 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_906 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.Surjection._.Eq₂.setoid
d_setoid_908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_908 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_908 v4 v5 v6
du_setoid_908 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_908 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_66
         (coe du_isCongruent_724 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Surjection._.Eq₂.sym
d_sym_910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_910 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_910 v4 v5 v6
du_sym_910 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_910 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₂.trans
d_trans_912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_912 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_912 v4 v5 v6
du_trans_912 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_912 v0 v1 v2
  = let v3 = coe du_function_860 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Surjection.isSurjection
d_isSurjection_914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
d_isSurjection_914 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSurjection_914 v4 v5 v6
du_isSurjection_914 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
du_isSurjection_914 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsSurjection'46'constructor_6463
      (coe
         du_isCongruent_724 (coe v0) (coe v1)
         (coe du_function_860 (coe v2)))
      (coe d_surjective_858 (coe v2))
-- Function.Bundles._.Surjection._.strictlySurjective
d_strictlySurjective_918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_918 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlySurjective_918 v4 v5 v6
du_strictlySurjective_918 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective_918 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlySurjective_230
      (coe du_isSurjection_914 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.Surjection.to⁻
d_to'8315'_920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny
d_to'8315'_920 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_to'8315'_920 v6 v7
du_to'8315'_920 :: T_Surjection_846 -> AgdaAny -> AgdaAny
du_to'8315'_920 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_surjective_858 v0 v1)
-- Function.Bundles._.Surjection.to∘to⁻
d_to'8728'to'8315'_924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny
d_to'8728'to'8315'_924 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_to'8728'to'8315'_924 v4 v5 v6 v7
du_to'8728'to'8315'_924 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Surjection_846 -> AgdaAny -> AgdaAny
du_to'8728'to'8315'_924 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Function.Structures.du_strictlySurjective_230
         (coe du_isSurjection_914 (coe v0) (coe v1) (coe v2)) (coe v3))
-- Function.Bundles._.Bijection
d_Bijection_926 a0 a1 a2 a3 a4 a5 = ()
data T_Bijection_926
  = C_Bijection'46'constructor_15277 (AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Function.Bundles._.Bijection.to
d_to_934 :: T_Bijection_926 -> AgdaAny -> AgdaAny
d_to_934 v0
  = case coe v0 of
      C_Bijection'46'constructor_15277 v1 v2 v3 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Bijection.cong
d_cong_936 ::
  T_Bijection_926 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_936 v0
  = case coe v0 of
      C_Bijection'46'constructor_15277 v1 v2 v3 -> coe v2
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Bijection.bijective
d_bijective_938 ::
  T_Bijection_926 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bijective_938 v0
  = case coe v0 of
      C_Bijection'46'constructor_15277 v1 v2 v3 -> coe v3
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Bijection.injective
d_injective_940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_940 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_injective_940 v6 v7 v8
du_injective_940 ::
  T_Bijection_926 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_injective_940 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (d_bijective_938 (coe v0))
      v1 v2
-- Function.Bundles._.Bijection.surjective
d_surjective_942 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_942 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_surjective_942 v6
du_surjective_942 ::
  T_Bijection_926 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_surjective_942 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_bijective_938 (coe v0))
-- Function.Bundles._.Bijection.injection
d_injection_944 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> T_Injection_776
d_injection_944 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_injection_944 v6
du_injection_944 :: T_Bijection_926 -> T_Injection_776
du_injection_944 v0
  = coe
      C_Injection'46'constructor_8675 (coe d_to_934 (coe v0))
      (coe d_cong_936 (coe v0)) (coe du_injective_940 (coe v0))
-- Function.Bundles._.Bijection.surjection
d_surjection_946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> T_Surjection_846
d_surjection_946 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_surjection_946 v6
du_surjection_946 :: T_Bijection_926 -> T_Surjection_846
du_surjection_946 v0
  = coe
      C_Surjection'46'constructor_11197 (coe d_to_934 (coe v0))
      (coe d_cong_936 (coe v0)) (coe du_surjective_942 (coe v0))
-- Function.Bundles._.Bijection._.isInjection
d_isInjection_950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
d_isInjection_950 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isInjection_950 v4 v5 v6
du_isInjection_950 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
du_isInjection_950 v0 v1 v2
  = coe
      du_isInjection_844 (coe v0) (coe v1)
      (coe du_injection_944 (coe v2))
-- Function.Bundles._.Bijection._.isSurjection
d_isSurjection_954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
d_isSurjection_954 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSurjection_954 v4 v5 v6
du_isSurjection_954 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
du_isSurjection_954 v0 v1 v2
  = coe
      du_isSurjection_914 (coe v0) (coe v1)
      (coe du_surjection_946 (coe v2))
-- Function.Bundles._.Bijection._.strictlySurjective
d_strictlySurjective_956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_956 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlySurjective_956 v4 v5 v6
du_strictlySurjective_956 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective_956 v0 v1 v2
  = let v3 = coe du_surjection_946 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_strictlySurjective_230
         (coe du_isSurjection_914 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Bijection._.to⁻
d_to'8315'_958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny
d_to'8315'_958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_to'8315'_958 v6
du_to'8315'_958 :: T_Bijection_926 -> AgdaAny -> AgdaAny
du_to'8315'_958 v0
  = coe du_to'8315'_920 (coe du_surjection_946 (coe v0))
-- Function.Bundles._.Bijection.isBijection
d_isBijection_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
d_isBijection_960 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isBijection_960 v4 v5 v6
du_isBijection_960 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
du_isBijection_960 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsBijection'46'constructor_10113
      (coe
         du_isInjection_844 (coe v0) (coe v1)
         (coe du_injection_944 (coe v2)))
      (coe du_surjective_942 (coe v2))
-- Function.Bundles._.Bijection._.Eq₁._≈_
d__'8776'__966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> ()
d__'8776'__966 = erased
-- Function.Bundles._.Bijection._.Eq₁._≉_
d__'8777'__968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> ()
d__'8777'__968 = erased
-- Function.Bundles._.Bijection._.Eq₁.Carrier
d_Carrier_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> ()
d_Carrier_970 = erased
-- Function.Bundles._.Bijection._.Eq₁.isEquivalence
d_isEquivalence_972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_972 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_972 v4 v5 v6
du_isEquivalence_972 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_972 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v5))))
-- Function.Bundles._.Bijection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_974 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_974 v4 v5 v6
du_isPartialEquivalence_974 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_974 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₁.partialSetoid
d_partialSetoid_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_976 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_976 v4 v5 v6
du_partialSetoid_976 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_976 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
               (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5)))))
-- Function.Bundles._.Bijection._.Eq₁.refl
d_refl_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny
d_refl_978 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_978 v4 v5 v6
du_refl_978 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny
du_refl_978 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (coe
                  MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
                  (coe v5)))))
-- Function.Bundles._.Bijection._.Eq₁.reflexive
d_reflexive_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_980 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_980 v4 v5 v6
du_reflexive_980 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_980 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (\ v7 v8 v9 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v6))
                    v7))))
-- Function.Bundles._.Bijection._.Eq₁.setoid
d_setoid_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_982 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_982 v4 v5 v6
du_setoid_982 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_982 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_40
            (coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4))))
-- Function.Bundles._.Bijection._.Eq₁.sym
d_sym_984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_984 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_984 v4 v5 v6
du_sym_984 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_984 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₁.trans
d_trans_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_986 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_986 v4 v5 v6
du_trans_986 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_986 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₂._≈_
d__'8776'__990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> ()
d__'8776'__990 = erased
-- Function.Bundles._.Bijection._.Eq₂._≉_
d__'8777'__992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> ()
d__'8777'__992 = erased
-- Function.Bundles._.Bijection._.Eq₂.Carrier
d_Carrier_994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> ()
d_Carrier_994 = erased
-- Function.Bundles._.Bijection._.Eq₂.isEquivalence
d_isEquivalence_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_996 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_996 v4 v5 v6
du_isEquivalence_996 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_996 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v5))))
-- Function.Bundles._.Bijection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_998 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_998 v4 v5 v6
du_isPartialEquivalence_998 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_998 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₂.partialSetoid
d_partialSetoid_1000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1000 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1000 v4 v5 v6
du_partialSetoid_1000 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1000 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
               (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5)))))
-- Function.Bundles._.Bijection._.Eq₂.refl
d_refl_1002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny
d_refl_1002 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1002 v4 v5 v6
du_refl_1002 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny
du_refl_1002 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (coe
                  MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
                  (coe v5)))))
-- Function.Bundles._.Bijection._.Eq₂.reflexive
d_reflexive_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1004 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1004 v4 v5 v6
du_reflexive_1004 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1004 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5) in
             coe
               (\ v7 v8 v9 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v6))
                    v7))))
-- Function.Bundles._.Bijection._.Eq₂.setoid
d_setoid_1006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1006 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1006 v4 v5 v6
du_setoid_1006 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1006 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_66
            (coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4))))
-- Function.Bundles._.Bijection._.Eq₂.sym
d_sym_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1008 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1008 v4 v5 v6
du_sym_1008 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1008 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₂.trans
d_trans_1010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1010 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1010 v4 v5 v6
du_trans_1010 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Bijection_926 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1010 v0 v1 v2
  = let v3 = coe du_isBijection_960 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._._._≈_
d__'8776'__1030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1030 = erased
-- Function.Bundles._._.Carrier
d_Carrier_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 -> ()
d_Carrier_1032 = erased
-- Function.Bundles._._.IsBiInverse
d_IsBiInverse_1044 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Function.Bundles._._.IsCongruent
d_IsCongruent_1048 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsInverse
d_IsInverse_1052 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Function.Bundles._._.IsLeftInverse
d_IsLeftInverse_1054 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Function.Bundles._._.IsRightInverse
d_IsRightInverse_1056 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Function.Bundles._._.IsSplitSurjection
d_IsSplitSurjection_1058 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsBiInverse.from₁-cong
d_from'8321''45'cong_1126 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8321''45'cong_1126 v0
  = coe
      MAlonzo.Code.Function.Structures.d_from'8321''45'cong_686 (coe v0)
-- Function.Bundles._._.IsBiInverse.from₂-cong
d_from'8322''45'cong_1128 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8322''45'cong_1128 v0
  = coe
      MAlonzo.Code.Function.Structures.d_from'8322''45'cong_688 (coe v0)
-- Function.Bundles._._.IsBiInverse.inverseʳ
d_inverse'691'_1130 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_1130 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_692 (coe v0)
-- Function.Bundles._._.IsBiInverse.inverseˡ
d_inverse'737'_1132 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_1132 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'737'_690 (coe v0)
-- Function.Bundles._._.IsBiInverse.to-isCongruent
d_to'45'isCongruent_1140 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_666 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_to'45'isCongruent_1140 v0
  = coe
      MAlonzo.Code.Function.Structures.d_to'45'isCongruent_684 (coe v0)
-- Function.Bundles._._.IsCongruent.cong
d_cong_1262 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1262 v0
  = coe MAlonzo.Code.Function.Structures.d_cong_32 (coe v0)
-- Function.Bundles._._.IsCongruent.isEquivalence₁
d_isEquivalence'8321'_1264 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_1264 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Bundles._._.IsCongruent.isEquivalence₂
d_isEquivalence'8322'_1266 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_1266 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Bundles._._.IsInverse.inverseʳ
d_inverse'691'_1382 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_1382 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_502 (coe v0)
-- Function.Bundles._._.IsInverse.isLeftInverse
d_isLeftInverse_1392 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_1392 v0
  = coe MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0)
-- Function.Bundles._._.IsInverse.Eq₁._≈_
d__'8776'__1406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1406 = erased
-- Function.Bundles._._.IsInverse.Eq₁._≉_
d__'8777'__1408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1408 = erased
-- Function.Bundles._._.IsInverse.Eq₁.Carrier
d_Carrier_1410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 -> ()
d_Carrier_1410 = erased
-- Function.Bundles._._.IsInverse.Eq₁.isEquivalence
d_isEquivalence_1412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1412 v8
du_isEquivalence_1412 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1412 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v2)))
-- Function.Bundles._._.IsInverse.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1414 v8
du_isPartialEquivalence_1414 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1414 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₁.partialSetoid
d_partialSetoid_1416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1416 v8
du_partialSetoid_1416 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1416 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2))))
-- Function.Bundles._._.IsInverse.Eq₁.refl
d_refl_1418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny
d_refl_1418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1418 v8
du_refl_1418 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny
du_refl_1418 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v2))))
-- Function.Bundles._._.IsInverse.Eq₁.reflexive
d_reflexive_1420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1420 v8
du_reflexive_1420 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1420 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Bundles._._.IsInverse.Eq₁.setoid
d_setoid_1422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1422 v8
du_setoid_1422 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1422 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1)))
-- Function.Bundles._._.IsInverse.Eq₁.sym
d_sym_1424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1424 v8
du_sym_1424 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1424 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₁.trans
d_trans_1426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1426 v8
du_trans_1426 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1426 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₂._≈_
d__'8776'__1430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1430 = erased
-- Function.Bundles._._.IsInverse.Eq₂._≉_
d__'8777'__1432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1432 = erased
-- Function.Bundles._._.IsInverse.Eq₂.Carrier
d_Carrier_1434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 -> ()
d_Carrier_1434 = erased
-- Function.Bundles._._.IsInverse.Eq₂.isEquivalence
d_isEquivalence_1436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1436 v8
du_isEquivalence_1436 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1436 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v2)))
-- Function.Bundles._._.IsInverse.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1438 v8
du_isPartialEquivalence_1438 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1438 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₂.partialSetoid
d_partialSetoid_1440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1440 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1440 v8
du_partialSetoid_1440 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1440 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2))))
-- Function.Bundles._._.IsInverse.Eq₂.refl
d_refl_1442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny
d_refl_1442 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1442 v8
du_refl_1442 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny
du_refl_1442 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v2))))
-- Function.Bundles._._.IsInverse.Eq₂.reflexive
d_reflexive_1444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1444 v8
du_reflexive_1444 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1444 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Bundles._._.IsInverse.Eq₂.setoid
d_setoid_1446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1446 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1446 v8
du_setoid_1446 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1446 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_66
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1)))
-- Function.Bundles._._.IsInverse.Eq₂.sym
d_sym_1448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1448 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1448 v8
du_sym_1448 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1448 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₂.trans
d_trans_1450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1450 v8
du_trans_1450 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1450 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Bundles._._.IsLeftInverse.from-cong
d_from'45'cong_1454 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1454 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_336 (coe v0)
-- Function.Bundles._._.IsLeftInverse.inverseˡ
d_inverse'737'_1456 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_1456 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'737'_338 (coe v0)
-- Function.Bundles._._.IsLeftInverse.isCongruent
d_isCongruent_1458 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1458 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0)
-- Function.Bundles._._.IsLeftInverse.isSurjection
d_isSurjection_1464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
d_isSurjection_1464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_isSurjection_1464
du_isSurjection_1464 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
du_isSurjection_1464 v0 v1 v2
  = coe MAlonzo.Code.Function.Structures.du_isSurjection_400 v1 v2
-- Function.Bundles._._.IsLeftInverse.strictlyInverseˡ
d_strictlyInverse'737'_1466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny
d_strictlyInverse'737'_1466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_strictlyInverse'737'_1466
du_strictlyInverse'737'_1466 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny
du_strictlyInverse'737'_1466 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'737'_396 v1 v2
      v3
-- Function.Bundles._._.IsLeftInverse.Eq₁._≈_
d__'8776'__1472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1472 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₁._≉_
d__'8777'__1474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1474 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₁.Carrier
d_Carrier_1476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 -> ()
d_Carrier_1476 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₁.isEquivalence
d_isEquivalence_1478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1478 v8
du_isEquivalence_1478 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1478 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v1))
-- Function.Bundles._._.IsLeftInverse.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1480 v8
du_isPartialEquivalence_1480 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1480 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₁.partialSetoid
d_partialSetoid_1482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1482 v8
du_partialSetoid_1482 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1482 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1)))
-- Function.Bundles._._.IsLeftInverse.Eq₁.refl
d_refl_1484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny
d_refl_1484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1484 v8
du_refl_1484 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny
du_refl_1484 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v1)))
-- Function.Bundles._._.IsLeftInverse.Eq₁.reflexive
d_reflexive_1486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1486 v8
du_reflexive_1486 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1486 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Bundles._._.IsLeftInverse.Eq₁.setoid
d_setoid_1488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1488 v8
du_setoid_1488 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1488 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0))
-- Function.Bundles._._.IsLeftInverse.Eq₁.sym
d_sym_1490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1490 v8
du_sym_1490 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1490 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₁.trans
d_trans_1492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1492 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1492 v8
du_trans_1492 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1492 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₂._≈_
d__'8776'__1496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1496 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₂._≉_
d__'8777'__1498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1498 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₂.Carrier
d_Carrier_1500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 -> ()
d_Carrier_1500 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₂.isEquivalence
d_isEquivalence_1502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1502 v8
du_isEquivalence_1502 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1502 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v1))
-- Function.Bundles._._.IsLeftInverse.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1504 v8
du_isPartialEquivalence_1504 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1504 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₂.partialSetoid
d_partialSetoid_1506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1506 v8
du_partialSetoid_1506 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1506 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1)))
-- Function.Bundles._._.IsLeftInverse.Eq₂.refl
d_refl_1508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny
d_refl_1508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1508 v8
du_refl_1508 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny
du_refl_1508 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v1)))
-- Function.Bundles._._.IsLeftInverse.Eq₂.reflexive
d_reflexive_1510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1510 v8
du_reflexive_1510 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1510 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Bundles._._.IsLeftInverse.Eq₂.setoid
d_setoid_1512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1512 v8
du_setoid_1512 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1512 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_66
      (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0))
-- Function.Bundles._._.IsLeftInverse.Eq₂.sym
d_sym_1514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1514 v8
du_sym_1514 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1514 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₂.trans
d_trans_1516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1516 v8
du_trans_1516 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1516 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsRightInverse.from-cong
d_from'45'cong_1520 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1520 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_422 (coe v0)
-- Function.Bundles._._.IsRightInverse.inverseʳ
d_inverse'691'_1522 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_1522 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_424 (coe v0)
-- Function.Bundles._._.IsRightInverse.isCongruent
d_isCongruent_1524 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1524 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0)
-- Function.Bundles._._.IsRightInverse.strictlyInverseʳ
d_strictlyInverse'691'_1530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny
d_strictlyInverse'691'_1530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_strictlyInverse'691'_1530
du_strictlyInverse'691'_1530 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny
du_strictlyInverse'691'_1530 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'691'_482 v0 v2
      v3
-- Function.Bundles._._.IsRightInverse.Eq₁._≈_
d__'8776'__1536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1536 = erased
-- Function.Bundles._._.IsRightInverse.Eq₁._≉_
d__'8777'__1538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1538 = erased
-- Function.Bundles._._.IsRightInverse.Eq₁.Carrier
d_Carrier_1540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 -> ()
d_Carrier_1540 = erased
-- Function.Bundles._._.IsRightInverse.Eq₁.isEquivalence
d_isEquivalence_1542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1542 v8
du_isEquivalence_1542 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1542 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v1))
-- Function.Bundles._._.IsRightInverse.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1544 v8
du_isPartialEquivalence_1544 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1544 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₁.partialSetoid
d_partialSetoid_1546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1546 v8
du_partialSetoid_1546 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1546 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1)))
-- Function.Bundles._._.IsRightInverse.Eq₁.refl
d_refl_1548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny
d_refl_1548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1548 v8
du_refl_1548 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny
du_refl_1548 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v1)))
-- Function.Bundles._._.IsRightInverse.Eq₁.reflexive
d_reflexive_1550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1550 v8
du_reflexive_1550 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1550 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Bundles._._.IsRightInverse.Eq₁.setoid
d_setoid_1552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1552 v8
du_setoid_1552 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1552 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0))
-- Function.Bundles._._.IsRightInverse.Eq₁.sym
d_sym_1554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1554 v8
du_sym_1554 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1554 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₁.trans
d_trans_1556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1556 v8
du_trans_1556 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1556 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₂._≈_
d__'8776'__1560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1560 = erased
-- Function.Bundles._._.IsRightInverse.Eq₂._≉_
d__'8777'__1562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1562 = erased
-- Function.Bundles._._.IsRightInverse.Eq₂.Carrier
d_Carrier_1564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 -> ()
d_Carrier_1564 = erased
-- Function.Bundles._._.IsRightInverse.Eq₂.isEquivalence
d_isEquivalence_1566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1566 v8
du_isEquivalence_1566 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1566 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v1))
-- Function.Bundles._._.IsRightInverse.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1568 v8
du_isPartialEquivalence_1568 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1568 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₂.partialSetoid
d_partialSetoid_1570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1570 v8
du_partialSetoid_1570 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1570 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1)))
-- Function.Bundles._._.IsRightInverse.Eq₂.refl
d_refl_1572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny
d_refl_1572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1572 v8
du_refl_1572 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny
du_refl_1572 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v1)))
-- Function.Bundles._._.IsRightInverse.Eq₂.reflexive
d_reflexive_1574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1574 v8
du_reflexive_1574 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1574 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Bundles._._.IsRightInverse.Eq₂.setoid
d_setoid_1576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1576 v8
du_setoid_1576 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1576 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_66
      (coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0))
-- Function.Bundles._._.IsRightInverse.Eq₂.sym
d_sym_1578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1578 v8
du_sym_1578 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1578 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₂.trans
d_trans_1580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1580 v8
du_trans_1580 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1580 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Bundles._._.IsSplitSurjection.from
d_from_1584 ::
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_752 ->
  AgdaAny -> AgdaAny
d_from_1584 v0
  = coe MAlonzo.Code.Function.Structures.d_from_760 (coe v0)
-- Function.Bundles._._.IsSplitSurjection.isLeftInverse
d_isLeftInverse_1596 ::
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_752 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_1596 v0
  = coe MAlonzo.Code.Function.Structures.d_isLeftInverse_762 (coe v0)
-- Function.Bundles._.Equivalence
d_Equivalence_1714 a0 a1 a2 a3 a4 a5 = ()
data T_Equivalence_1714
  = C_Equivalence'46'constructor_25797 (AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.Equivalence.to
d_to_1724 :: T_Equivalence_1714 -> AgdaAny -> AgdaAny
d_to_1724 v0
  = case coe v0 of
      C_Equivalence'46'constructor_25797 v1 v2 v3 v4 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Equivalence.from
d_from_1726 :: T_Equivalence_1714 -> AgdaAny -> AgdaAny
d_from_1726 v0
  = case coe v0 of
      C_Equivalence'46'constructor_25797 v1 v2 v3 v4 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Equivalence.to-cong
d_to'45'cong_1728 ::
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_1728 v0
  = case coe v0 of
      C_Equivalence'46'constructor_25797 v1 v2 v3 v4 -> coe v3
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Equivalence.from-cong
d_from'45'cong_1730 ::
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1730 v0
  = case coe v0 of
      C_Equivalence'46'constructor_25797 v1 v2 v3 v4 -> coe v4
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Equivalence.toFunction
d_toFunction_1732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> T_Func_714
d_toFunction_1732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_toFunction_1732 v6
du_toFunction_1732 :: T_Equivalence_1714 -> T_Func_714
du_toFunction_1732 v0
  = coe
      C_Func'46'constructor_6307 (coe d_to_1724 (coe v0))
      (coe d_to'45'cong_1728 (coe v0))
-- Function.Bundles._.Equivalence._.isCongruent
d_isCongruent_1736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1736 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_1736 v4 v5 v6
du_isCongruent_1736 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_1736 v0 v1 v2
  = coe
      du_isCongruent_724 (coe v0) (coe v1)
      (coe du_toFunction_1732 (coe v2))
-- Function.Bundles._.Equivalence._.Eq₁._≈_
d__'8776'__1740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1740 = erased
-- Function.Bundles._.Equivalence._.Eq₁._≉_
d__'8777'__1742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1742 = erased
-- Function.Bundles._.Equivalence._.Eq₁.Carrier
d_Carrier_1744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> ()
d_Carrier_1744 = erased
-- Function.Bundles._.Equivalence._.Eq₁.isEquivalence
d_isEquivalence_1746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1746 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1746 v4 v5 v6
du_isEquivalence_1746 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1746 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.Equivalence._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1748 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1748 v4 v5 v6
du_isPartialEquivalence_1748 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1748 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₁.partialSetoid
d_partialSetoid_1750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1750 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1750 v4 v5 v6
du_partialSetoid_1750 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1750 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.Equivalence._.Eq₁.refl
d_refl_1752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny
d_refl_1752 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1752 v4 v5 v6
du_refl_1752 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny
du_refl_1752 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.Equivalence._.Eq₁.reflexive
d_reflexive_1754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1754 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1754 v4 v5 v6
du_reflexive_1754 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1754 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.Equivalence._.Eq₁.setoid
d_setoid_1756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1756 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1756 v4 v5 v6
du_setoid_1756 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1756 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe du_isCongruent_724 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Equivalence._.Eq₁.sym
d_sym_1758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1758 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1758 v4 v5 v6
du_sym_1758 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1758 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₁.trans
d_trans_1760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1760 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1760 v4 v5 v6
du_trans_1760 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1760 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₂._≈_
d__'8776'__1764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1764 = erased
-- Function.Bundles._.Equivalence._.Eq₂._≉_
d__'8777'__1766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1766 = erased
-- Function.Bundles._.Equivalence._.Eq₂.Carrier
d_Carrier_1768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> ()
d_Carrier_1768 = erased
-- Function.Bundles._.Equivalence._.Eq₂.isEquivalence
d_isEquivalence_1770 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1770 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1770 v4 v5 v6
du_isEquivalence_1770 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1770 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.Equivalence._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1772 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1772 v4 v5 v6
du_isPartialEquivalence_1772 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1772 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₂.partialSetoid
d_partialSetoid_1774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1774 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1774 v4 v5 v6
du_partialSetoid_1774 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1774 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4))))
-- Function.Bundles._.Equivalence._.Eq₂.refl
d_refl_1776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny
d_refl_1776 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1776 v4 v5 v6
du_refl_1776 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny
du_refl_1776 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.Equivalence._.Eq₂.reflexive
d_reflexive_1778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1778 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1778 v4 v5 v6
du_reflexive_1778 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1778 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.Equivalence._.Eq₂.setoid
d_setoid_1780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1780 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1780 v4 v5 v6
du_setoid_1780 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1780 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_66
         (coe du_isCongruent_724 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Equivalence._.Eq₂.sym
d_sym_1782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1782 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1782 v4 v5 v6
du_sym_1782 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1782 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₂.trans
d_trans_1784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1784 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1784 v4 v5 v6
du_trans_1784 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1784 v0 v1 v2
  = let v3 = coe du_toFunction_1732 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_724 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.Equivalence.fromFunction
d_fromFunction_1786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 -> T_Func_714
d_fromFunction_1786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_fromFunction_1786 v6
du_fromFunction_1786 :: T_Equivalence_1714 -> T_Func_714
du_fromFunction_1786 v0
  = coe
      C_Func'46'constructor_6307 (coe d_from_1726 (coe v0))
      (coe d_from'45'cong_1730 (coe v0))
-- Function.Bundles._.Equivalence._.isCongruent
d_isCongruent_1790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1790 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_1790 v4 v5 v6
du_isCongruent_1790 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Equivalence_1714 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_1790 v0 v1 v2
  = coe
      du_isCongruent_724 (coe v1) (coe v0)
      (coe du_fromFunction_1786 (coe v2))
-- Function.Bundles._.LeftInverse
d_LeftInverse_1792 a0 a1 a2 a3 a4 a5 = ()
data T_LeftInverse_1792
  = C_LeftInverse'46'constructor_29775 (AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.LeftInverse.to
d_to_1804 :: T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_to_1804 v0
  = case coe v0 of
      C_LeftInverse'46'constructor_29775 v1 v2 v3 v4 v5 -> coe v1
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.from
d_from_1806 :: T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_from_1806 v0
  = case coe v0 of
      C_LeftInverse'46'constructor_29775 v1 v2 v3 v4 v5 -> coe v2
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.to-cong
d_to'45'cong_1808 ::
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_1808 v0
  = case coe v0 of
      C_LeftInverse'46'constructor_29775 v1 v2 v3 v4 v5 -> coe v3
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.from-cong
d_from'45'cong_1810 ::
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1810 v0
  = case coe v0 of
      C_LeftInverse'46'constructor_29775 v1 v2 v3 v4 v5 -> coe v4
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.inverseˡ
d_inverse'737'_1812 ::
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_1812 v0
  = case coe v0 of
      C_LeftInverse'46'constructor_29775 v1 v2 v3 v4 v5 -> coe v5
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.isCongruent
d_isCongruent_1814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1814 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_1814 v4 v5 v6
du_isCongruent_1814 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_1814 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsCongruent'46'constructor_985
      (coe d_to'45'cong_1808 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
-- Function.Bundles._.LeftInverse.isLeftInverse
d_isLeftInverse_1816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_1816 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isLeftInverse_1816 v4 v5 v6
du_isLeftInverse_1816 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
du_isLeftInverse_1816 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsLeftInverse'46'constructor_14363
      (coe du_isCongruent_1814 (coe v0) (coe v1) (coe v2))
      (coe d_from'45'cong_1810 (coe v2))
      (coe d_inverse'737'_1812 (coe v2))
-- Function.Bundles._.LeftInverse._.isSurjection
d_isSurjection_1820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
d_isSurjection_1820 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSurjection_1820 v4 v5 v6
du_isSurjection_1820 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
du_isSurjection_1820 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_isSurjection_400
      (coe d_from_1806 (coe v2))
      (coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.LeftInverse._.strictlyInverseˡ
d_strictlyInverse'737'_1822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_1822 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'737'_1822 v4 v5 v6
du_strictlyInverse'737'_1822 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_1822 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'737'_396
      (coe d_from_1806 (coe v2))
      (coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.LeftInverse._.Eq₁._≈_
d__'8776'__1826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1826 = erased
-- Function.Bundles._.LeftInverse._.Eq₁._≉_
d__'8777'__1828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1828 = erased
-- Function.Bundles._.LeftInverse._.Eq₁.Carrier
d_Carrier_1830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> ()
d_Carrier_1830 = erased
-- Function.Bundles._.LeftInverse._.Eq₁.isEquivalence
d_isEquivalence_1832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1832 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1832 v4 v5 v6
du_isEquivalence_1832 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1832 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.LeftInverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1834 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1834 v4 v5 v6
du_isPartialEquivalence_1834 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1834 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₁.partialSetoid
d_partialSetoid_1836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1836 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1836 v4 v5 v6
du_partialSetoid_1836 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1836 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.LeftInverse._.Eq₁.refl
d_refl_1838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_refl_1838 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1838 v4 v5 v6
du_refl_1838 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
du_refl_1838 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.LeftInverse._.Eq₁.reflexive
d_reflexive_1840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1840 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1840 v4 v5 v6
du_reflexive_1840 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1840 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.LeftInverse._.Eq₁.setoid
d_setoid_1842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1842 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1842 v4 v5 v6
du_setoid_1842 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1842 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3)))
-- Function.Bundles._.LeftInverse._.Eq₁.sym
d_sym_1844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1844 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1844 v4 v5 v6
du_sym_1844 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1844 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₁.trans
d_trans_1846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1846 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1846 v4 v5 v6
du_trans_1846 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1846 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₂._≈_
d__'8776'__1850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1850 = erased
-- Function.Bundles._.LeftInverse._.Eq₂._≉_
d__'8777'__1852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1852 = erased
-- Function.Bundles._.LeftInverse._.Eq₂.Carrier
d_Carrier_1854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> ()
d_Carrier_1854 = erased
-- Function.Bundles._.LeftInverse._.Eq₂.isEquivalence
d_isEquivalence_1856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1856 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1856 v4 v5 v6
du_isEquivalence_1856 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1856 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.LeftInverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1858 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1858 v4 v5 v6
du_isPartialEquivalence_1858 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1858 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₂.partialSetoid
d_partialSetoid_1860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1860 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1860 v4 v5 v6
du_partialSetoid_1860 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1860 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4))))
-- Function.Bundles._.LeftInverse._.Eq₂.refl
d_refl_1862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_refl_1862 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1862 v4 v5 v6
du_refl_1862 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
du_refl_1862 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.LeftInverse._.Eq₂.reflexive
d_reflexive_1864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1864 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1864 v4 v5 v6
du_reflexive_1864 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1864 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.LeftInverse._.Eq₂.setoid
d_setoid_1866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1866 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1866 v4 v5 v6
du_setoid_1866 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1866 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_66
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3)))
-- Function.Bundles._.LeftInverse._.Eq₂.sym
d_sym_1868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1868 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1868 v4 v5 v6
du_sym_1868 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1868 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₂.trans
d_trans_1870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1870 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1870 v4 v5 v6
du_trans_1870 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1870 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.LeftInverse.equivalence
d_equivalence_1872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> T_Equivalence_1714
d_equivalence_1872 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equivalence_1872 v6
du_equivalence_1872 :: T_LeftInverse_1792 -> T_Equivalence_1714
du_equivalence_1872 v0
  = coe
      C_Equivalence'46'constructor_25797 (coe d_to_1804 (coe v0))
      (coe d_from_1806 (coe v0)) (coe d_to'45'cong_1808 (coe v0))
      (coe d_from'45'cong_1810 (coe v0))
-- Function.Bundles._.LeftInverse.isSplitSurjection
d_isSplitSurjection_1874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_752
d_isSplitSurjection_1874 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSplitSurjection_1874 v4 v5 v6
du_isSplitSurjection_1874 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_752
du_isSplitSurjection_1874 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsSplitSurjection'46'constructor_35501
      (coe d_from_1806 (coe v2))
      (coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.LeftInverse.surjection
d_surjection_1876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> T_Surjection_846
d_surjection_1876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_surjection_1876 v6
du_surjection_1876 :: T_LeftInverse_1792 -> T_Surjection_846
du_surjection_1876 v0
  = coe
      C_Surjection'46'constructor_11197 (coe d_to_1804 (coe v0))
      (coe d_to'45'cong_1808 (coe v0))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_from_1806 v0 v1)
              (coe d_inverse'737'_1812 v0 v1)))
-- Function.Bundles._.RightInverse
d_RightInverse_1880 a0 a1 a2 a3 a4 a5 = ()
data T_RightInverse_1880
  = C_RightInverse'46'constructor_34573 (AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.RightInverse.to
d_to_1892 :: T_RightInverse_1880 -> AgdaAny -> AgdaAny
d_to_1892 v0
  = case coe v0 of
      C_RightInverse'46'constructor_34573 v1 v2 v3 v4 v5 -> coe v1
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.from
d_from_1894 :: T_RightInverse_1880 -> AgdaAny -> AgdaAny
d_from_1894 v0
  = case coe v0 of
      C_RightInverse'46'constructor_34573 v1 v2 v3 v4 v5 -> coe v2
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.to-cong
d_to'45'cong_1896 ::
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_1896 v0
  = case coe v0 of
      C_RightInverse'46'constructor_34573 v1 v2 v3 v4 v5 -> coe v3
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.from-cong
d_from'45'cong_1898 ::
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1898 v0
  = case coe v0 of
      C_RightInverse'46'constructor_34573 v1 v2 v3 v4 v5 -> coe v4
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.inverseʳ
d_inverse'691'_1900 ::
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_1900 v0
  = case coe v0 of
      C_RightInverse'46'constructor_34573 v1 v2 v3 v4 v5 -> coe v5
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.isCongruent
d_isCongruent_1902 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1902 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_1902 v4 v5 v6
du_isCongruent_1902 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_1902 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsCongruent'46'constructor_985
      (coe d_to'45'cong_1896 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
-- Function.Bundles._.RightInverse.isRightInverse
d_isRightInverse_1904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
d_isRightInverse_1904 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isRightInverse_1904 v4 v5 v6
du_isRightInverse_1904 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
du_isRightInverse_1904 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsRightInverse'46'constructor_18837
      (coe du_isCongruent_1902 (coe v0) (coe v1) (coe v2))
      (coe d_from'45'cong_1898 (coe v2))
      (coe d_inverse'691'_1900 (coe v2))
-- Function.Bundles._.RightInverse._.strictlyInverseʳ
d_strictlyInverse'691'_1908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny
d_strictlyInverse'691'_1908 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'691'_1908 v4 v5 v6
du_strictlyInverse'691'_1908 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny
du_strictlyInverse'691'_1908 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'691'_482
      (coe d_to_1892 (coe v2))
      (coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.RightInverse._.Eq₁._≈_
d__'8776'__1912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1912 = erased
-- Function.Bundles._.RightInverse._.Eq₁._≉_
d__'8777'__1914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1914 = erased
-- Function.Bundles._.RightInverse._.Eq₁.Carrier
d_Carrier_1916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> ()
d_Carrier_1916 = erased
-- Function.Bundles._.RightInverse._.Eq₁.isEquivalence
d_isEquivalence_1918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1918 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1918 v4 v5 v6
du_isEquivalence_1918 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1918 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.RightInverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1920 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1920 v4 v5 v6
du_isPartialEquivalence_1920 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1920 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₁.partialSetoid
d_partialSetoid_1922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1922 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1922 v4 v5 v6
du_partialSetoid_1922 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1922 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.RightInverse._.Eq₁.refl
d_refl_1924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny
d_refl_1924 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1924 v4 v5 v6
du_refl_1924 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny
du_refl_1924 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.RightInverse._.Eq₁.reflexive
d_reflexive_1926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1926 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1926 v4 v5 v6
du_reflexive_1926 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1926 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.RightInverse._.Eq₁.setoid
d_setoid_1928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1928 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1928 v4 v5 v6
du_setoid_1928 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1928 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3)))
-- Function.Bundles._.RightInverse._.Eq₁.sym
d_sym_1930 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1930 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1930 v4 v5 v6
du_sym_1930 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1930 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₁.trans
d_trans_1932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1932 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1932 v4 v5 v6
du_trans_1932 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1932 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₂._≈_
d__'8776'__1936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1936 = erased
-- Function.Bundles._.RightInverse._.Eq₂._≉_
d__'8777'__1938 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1938 = erased
-- Function.Bundles._.RightInverse._.Eq₂.Carrier
d_Carrier_1940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> ()
d_Carrier_1940 = erased
-- Function.Bundles._.RightInverse._.Eq₂.isEquivalence
d_isEquivalence_1942 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1942 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1942 v4 v5 v6
du_isEquivalence_1942 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1942 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.RightInverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1944 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1944 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1944 v4 v5 v6
du_isPartialEquivalence_1944 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1944 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₂.partialSetoid
d_partialSetoid_1946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1946 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1946 v4 v5 v6
du_partialSetoid_1946 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1946 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4))))
-- Function.Bundles._.RightInverse._.Eq₂.refl
d_refl_1948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny
d_refl_1948 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1948 v4 v5 v6
du_refl_1948 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny
du_refl_1948 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.RightInverse._.Eq₂.reflexive
d_reflexive_1950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1950 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1950 v4 v5 v6
du_reflexive_1950 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1950 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.RightInverse._.Eq₂.setoid
d_setoid_1952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1952 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1952 v4 v5 v6
du_setoid_1952 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1952 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_66
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3)))
-- Function.Bundles._.RightInverse._.Eq₂.sym
d_sym_1954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1954 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1954 v4 v5 v6
du_sym_1954 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1954 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₂.trans
d_trans_1956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1956 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1956 v4 v5 v6
du_trans_1956 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1956 v0 v1 v2
  = let v3 = coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.RightInverse.equivalence
d_equivalence_1958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_RightInverse_1880 -> T_Equivalence_1714
d_equivalence_1958 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equivalence_1958 v6
du_equivalence_1958 :: T_RightInverse_1880 -> T_Equivalence_1714
du_equivalence_1958 v0
  = coe
      C_Equivalence'46'constructor_25797 (coe d_to_1892 (coe v0))
      (coe d_from_1894 (coe v0)) (coe d_to'45'cong_1896 (coe v0))
      (coe d_from'45'cong_1898 (coe v0))
-- Function.Bundles._.Inverse
d_Inverse_1960 a0 a1 a2 a3 a4 a5 = ()
data T_Inverse_1960
  = C_Inverse'46'constructor_38621 (AgdaAny -> AgdaAny)
                                   (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                   (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Function.Bundles._.Inverse.to
d_to_1972 :: T_Inverse_1960 -> AgdaAny -> AgdaAny
d_to_1972 v0
  = case coe v0 of
      C_Inverse'46'constructor_38621 v1 v2 v3 v4 v5 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.from
d_from_1974 :: T_Inverse_1960 -> AgdaAny -> AgdaAny
d_from_1974 v0
  = case coe v0 of
      C_Inverse'46'constructor_38621 v1 v2 v3 v4 v5 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.to-cong
d_to'45'cong_1976 ::
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_1976 v0
  = case coe v0 of
      C_Inverse'46'constructor_38621 v1 v2 v3 v4 v5 -> coe v3
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.from-cong
d_from'45'cong_1978 ::
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1978 v0
  = case coe v0 of
      C_Inverse'46'constructor_38621 v1 v2 v3 v4 v5 -> coe v4
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.inverse
d_inverse_1980 ::
  T_Inverse_1960 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1980 v0
  = case coe v0 of
      C_Inverse'46'constructor_38621 v1 v2 v3 v4 v5 -> coe v5
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.inverseˡ
d_inverse'737'_1982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_1982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_inverse'737'_1982 v6 v7 v8
du_inverse'737'_1982 ::
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'737'_1982 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (d_inverse_1980 (coe v0))
      v1 v2
-- Function.Bundles._.Inverse.inverseʳ
d_inverse'691'_1984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_1984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_inverse'691'_1984 v6 v7 v8
du_inverse'691'_1984 ::
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691'_1984 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (d_inverse_1980 (coe v0))
      v1 v2
-- Function.Bundles._.Inverse.leftInverse
d_leftInverse_1986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> T_LeftInverse_1792
d_leftInverse_1986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_leftInverse_1986 v6
du_leftInverse_1986 :: T_Inverse_1960 -> T_LeftInverse_1792
du_leftInverse_1986 v0
  = coe
      C_LeftInverse'46'constructor_29775 (coe d_to_1972 (coe v0))
      (coe d_from_1974 (coe v0)) (coe d_to'45'cong_1976 (coe v0))
      (coe d_from'45'cong_1978 (coe v0))
      (coe du_inverse'737'_1982 (coe v0))
-- Function.Bundles._.Inverse.rightInverse
d_rightInverse_1988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> T_RightInverse_1880
d_rightInverse_1988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_rightInverse_1988 v6
du_rightInverse_1988 :: T_Inverse_1960 -> T_RightInverse_1880
du_rightInverse_1988 v0
  = coe
      C_RightInverse'46'constructor_34573 (coe d_to_1972 (coe v0))
      (coe d_from_1974 (coe v0)) (coe d_to'45'cong_1976 (coe v0))
      (coe d_from'45'cong_1978 (coe v0))
      (coe du_inverse'691'_1984 (coe v0))
-- Function.Bundles._.Inverse._.isLeftInverse
d_isLeftInverse_1992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_1992 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isLeftInverse_1992 v4 v5 v6
du_isLeftInverse_1992 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
du_isLeftInverse_1992 v0 v1 v2
  = coe
      du_isLeftInverse_1816 (coe v0) (coe v1)
      (coe du_leftInverse_1986 (coe v2))
-- Function.Bundles._.Inverse._.strictlyInverseˡ
d_strictlyInverse'737'_1994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_1994 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'737'_1994 v4 v5 v6
du_strictlyInverse'737'_1994 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_1994 v0 v1 v2
  = let v3 = coe du_leftInverse_1986 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_strictlyInverse'737'_396
         (coe d_from_1806 (coe v3))
         (coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Inverse._.isRightInverse
d_isRightInverse_1998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
d_isRightInverse_1998 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isRightInverse_1998 v4 v5 v6
du_isRightInverse_1998 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
du_isRightInverse_1998 v0 v1 v2
  = coe
      du_isRightInverse_1904 (coe v0) (coe v1)
      (coe du_rightInverse_1988 (coe v2))
-- Function.Bundles._.Inverse._.strictlyInverseʳ
d_strictlyInverse'691'_2000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny
d_strictlyInverse'691'_2000 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'691'_2000 v4 v5 v6
du_strictlyInverse'691'_2000 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny
du_strictlyInverse'691'_2000 v0 v1 v2
  = let v3 = coe du_rightInverse_1988 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_strictlyInverse'691'_482
         (coe d_to_1892 (coe v3))
         (coe du_isRightInverse_1904 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Inverse.isInverse
d_isInverse_2002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> MAlonzo.Code.Function.Structures.T_IsInverse_490
d_isInverse_2002 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isInverse_2002 v4 v5 v6
du_isInverse_2002 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> MAlonzo.Code.Function.Structures.T_IsInverse_490
du_isInverse_2002 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsInverse'46'constructor_22449
      (coe
         du_isLeftInverse_1816 (coe v0) (coe v1)
         (coe du_leftInverse_1986 (coe v2)))
      (coe du_inverse'691'_1984 (coe v2))
-- Function.Bundles._.Inverse._.Eq₁._≈_
d__'8776'__2008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2008 = erased
-- Function.Bundles._.Inverse._.Eq₁._≉_
d__'8777'__2010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2010 = erased
-- Function.Bundles._.Inverse._.Eq₁.Carrier
d_Carrier_2012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> ()
d_Carrier_2012 = erased
-- Function.Bundles._.Inverse._.Eq₁.isEquivalence
d_isEquivalence_2014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2014 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2014 v4 v5 v6
du_isEquivalence_2014 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2014 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v5))))
-- Function.Bundles._.Inverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_2016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2016 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2016 v4 v5 v6
du_isPartialEquivalence_2016 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2016 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₁.partialSetoid
d_partialSetoid_2018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2018 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2018 v4 v5 v6
du_partialSetoid_2018 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2018 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
               (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5)))))
-- Function.Bundles._.Inverse._.Eq₁.refl
d_refl_2020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny
d_refl_2020 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2020 v4 v5 v6
du_refl_2020 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny
du_refl_2020 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (coe
                  MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
                  (coe v5)))))
-- Function.Bundles._.Inverse._.Eq₁.reflexive
d_reflexive_2022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2022 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2022 v4 v5 v6
du_reflexive_2022 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2022 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (\ v7 v8 v9 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v6))
                    v7))))
-- Function.Bundles._.Inverse._.Eq₁.setoid
d_setoid_2024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2024 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2024 v4 v5 v6
du_setoid_2024 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2024 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_40
            (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4))))
-- Function.Bundles._.Inverse._.Eq₁.sym
d_sym_2026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2026 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2026 v4 v5 v6
du_sym_2026 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2026 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₁.trans
d_trans_2028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2028 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2028 v4 v5 v6
du_trans_2028 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2028 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₂._≈_
d__'8776'__2032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2032 = erased
-- Function.Bundles._.Inverse._.Eq₂._≉_
d__'8777'__2034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2034 = erased
-- Function.Bundles._.Inverse._.Eq₂.Carrier
d_Carrier_2036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> ()
d_Carrier_2036 = erased
-- Function.Bundles._.Inverse._.Eq₂.isEquivalence
d_isEquivalence_2038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2038 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2038 v4 v5 v6
du_isEquivalence_2038 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2038 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v5))))
-- Function.Bundles._.Inverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_2040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2040 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2040 v4 v5 v6
du_isPartialEquivalence_2040 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2040 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₂.partialSetoid
d_partialSetoid_2042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2042 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2042 v4 v5 v6
du_partialSetoid_2042 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2042 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
               (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5)))))
-- Function.Bundles._.Inverse._.Eq₂.refl
d_refl_2044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny
d_refl_2044 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2044 v4 v5 v6
du_refl_2044 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny
du_refl_2044 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (coe
                  MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
                  (coe v5)))))
-- Function.Bundles._.Inverse._.Eq₂.reflexive
d_reflexive_2046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2046 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2046 v4 v5 v6
du_reflexive_2046 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2046 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5) in
             coe
               (\ v7 v8 v9 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v6))
                    v7))))
-- Function.Bundles._.Inverse._.Eq₂.setoid
d_setoid_2048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2048 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2048 v4 v5 v6
du_setoid_2048 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2048 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_66
            (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4))))
-- Function.Bundles._.Inverse._.Eq₂.sym
d_sym_2050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2050 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2050 v4 v5 v6
du_sym_2050 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2050 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₂.trans
d_trans_2052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2052 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2052 v4 v5 v6
du_trans_2052 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_Inverse_1960 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2052 v0 v1 v2
  = let v3 = coe du_isInverse_2002 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v6))))))
-- Function.Bundles._.BiEquivalence
d_BiEquivalence_2054 a0 a1 a2 a3 a4 a5 = ()
data T_BiEquivalence_2054
  = C_BiEquivalence'46'constructor_44693 (AgdaAny -> AgdaAny)
                                         (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                         (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                         (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                         (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.BiEquivalence.to
d_to_2068 :: T_BiEquivalence_2054 -> AgdaAny -> AgdaAny
d_to_2068 v0
  = case coe v0 of
      C_BiEquivalence'46'constructor_44693 v1 v2 v3 v4 v5 v6 -> coe v1
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.from₁
d_from'8321'_2070 :: T_BiEquivalence_2054 -> AgdaAny -> AgdaAny
d_from'8321'_2070 v0
  = case coe v0 of
      C_BiEquivalence'46'constructor_44693 v1 v2 v3 v4 v5 v6 -> coe v2
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.from₂
d_from'8322'_2072 :: T_BiEquivalence_2054 -> AgdaAny -> AgdaAny
d_from'8322'_2072 v0
  = case coe v0 of
      C_BiEquivalence'46'constructor_44693 v1 v2 v3 v4 v5 v6 -> coe v3
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.to-cong
d_to'45'cong_2074 ::
  T_BiEquivalence_2054 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_2074 v0
  = case coe v0 of
      C_BiEquivalence'46'constructor_44693 v1 v2 v3 v4 v5 v6 -> coe v4
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.from₁-cong
d_from'8321''45'cong_2076 ::
  T_BiEquivalence_2054 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8321''45'cong_2076 v0
  = case coe v0 of
      C_BiEquivalence'46'constructor_44693 v1 v2 v3 v4 v5 v6 -> coe v5
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.from₂-cong
d_from'8322''45'cong_2078 ::
  T_BiEquivalence_2054 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8322''45'cong_2078 v0
  = case coe v0 of
      C_BiEquivalence'46'constructor_44693 v1 v2 v3 v4 v5 v6 -> coe v6
      _                                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse
d_BiInverse_2080 a0 a1 a2 a3 a4 a5 = ()
data T_BiInverse_2080
  = C_BiInverse'46'constructor_47439 (AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.BiInverse.to
d_to_2098 :: T_BiInverse_2080 -> AgdaAny -> AgdaAny
d_to_2098 v0
  = case coe v0 of
      C_BiInverse'46'constructor_47439 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.from₁
d_from'8321'_2100 :: T_BiInverse_2080 -> AgdaAny -> AgdaAny
d_from'8321'_2100 v0
  = case coe v0 of
      C_BiInverse'46'constructor_47439 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.from₂
d_from'8322'_2102 :: T_BiInverse_2080 -> AgdaAny -> AgdaAny
d_from'8322'_2102 v0
  = case coe v0 of
      C_BiInverse'46'constructor_47439 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.to-cong
d_to'45'cong_2104 ::
  T_BiInverse_2080 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_2104 v0
  = case coe v0 of
      C_BiInverse'46'constructor_47439 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.from₁-cong
d_from'8321''45'cong_2106 ::
  T_BiInverse_2080 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8321''45'cong_2106 v0
  = case coe v0 of
      C_BiInverse'46'constructor_47439 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.from₂-cong
d_from'8322''45'cong_2108 ::
  T_BiInverse_2080 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8322''45'cong_2108 v0
  = case coe v0 of
      C_BiInverse'46'constructor_47439 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.inverseˡ
d_inverse'737'_2110 ::
  T_BiInverse_2080 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_2110 v0
  = case coe v0 of
      C_BiInverse'46'constructor_47439 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.inverseʳ
d_inverse'691'_2112 ::
  T_BiInverse_2080 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_2112 v0
  = case coe v0 of
      C_BiInverse'46'constructor_47439 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _                                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.to-isCongruent
d_to'45'isCongruent_2114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_BiInverse_2080 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_to'45'isCongruent_2114 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_to'45'isCongruent_2114 v4 v5 v6
du_to'45'isCongruent_2114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_BiInverse_2080 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_to'45'isCongruent_2114 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsCongruent'46'constructor_985
      (coe d_to'45'cong_2104 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
-- Function.Bundles._.BiInverse.isBiInverse
d_isBiInverse_2116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_BiInverse_2080 ->
  MAlonzo.Code.Function.Structures.T_IsBiInverse_666
d_isBiInverse_2116 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isBiInverse_2116 v4 v5 v6
du_isBiInverse_2116 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_BiInverse_2080 ->
  MAlonzo.Code.Function.Structures.T_IsBiInverse_666
du_isBiInverse_2116 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsBiInverse'46'constructor_32731
      (coe du_to'45'isCongruent_2114 (coe v0) (coe v1) (coe v2))
      (coe d_from'8321''45'cong_2106 (coe v2))
      (coe d_from'8322''45'cong_2108 (coe v2))
      (coe d_inverse'737'_2110 (coe v2))
      (coe d_inverse'691'_2112 (coe v2))
-- Function.Bundles._.BiInverse.biEquivalence
d_biEquivalence_2118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_BiInverse_2080 -> T_BiEquivalence_2054
d_biEquivalence_2118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_biEquivalence_2118 v6
du_biEquivalence_2118 :: T_BiInverse_2080 -> T_BiEquivalence_2054
du_biEquivalence_2118 v0
  = coe
      C_BiEquivalence'46'constructor_44693 (coe d_to_2098 (coe v0))
      (coe d_from'8321'_2100 (coe v0)) (coe d_from'8322'_2102 (coe v0))
      (coe d_to'45'cong_2104 (coe v0))
      (coe d_from'8321''45'cong_2106 (coe v0))
      (coe d_from'8322''45'cong_2108 (coe v0))
-- Function.Bundles._.SplitSurjection
d_SplitSurjection_2120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 -> ()
d_SplitSurjection_2120 = erased
-- Function.Bundles._.SplitSurjection.equivalence
d_equivalence_2126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> T_Equivalence_1714
d_equivalence_2126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equivalence_2126 v6
du_equivalence_2126 :: T_LeftInverse_1792 -> T_Equivalence_1714
du_equivalence_2126 v0 = coe du_equivalence_1872 (coe v0)
-- Function.Bundles._.SplitSurjection.from
d_from_2128 :: T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_from_2128 v0 = coe d_from_1806 (coe v0)
-- Function.Bundles._.SplitSurjection.from-cong
d_from'45'cong_2130 ::
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_2130 v0 = coe d_from'45'cong_1810 (coe v0)
-- Function.Bundles._.SplitSurjection.inverseˡ
d_inverse'737'_2132 ::
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_2132 v0 = coe d_inverse'737'_1812 (coe v0)
-- Function.Bundles._.SplitSurjection.isCongruent
d_isCongruent_2134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_2134 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_2134 v4 v5 v6
du_isCongruent_2134 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_2134 v0 v1 v2
  = coe du_isCongruent_1814 (coe v0) (coe v1) (coe v2)
-- Function.Bundles._.SplitSurjection.isLeftInverse
d_isLeftInverse_2136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_2136 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isLeftInverse_2136 v4 v5 v6
du_isLeftInverse_2136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
du_isLeftInverse_2136 v0 v1 v2
  = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2)
-- Function.Bundles._.SplitSurjection.isSplitSurjection
d_isSplitSurjection_2138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_752
d_isSplitSurjection_2138 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSplitSurjection_2138 v4 v5 v6
du_isSplitSurjection_2138 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_752
du_isSplitSurjection_2138 v0 v1 v2
  = coe du_isSplitSurjection_1874 (coe v0) (coe v1) (coe v2)
-- Function.Bundles._.SplitSurjection.isSurjection
d_isSurjection_2140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
d_isSurjection_2140 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSurjection_2140 v4 v5 v6
du_isSurjection_2140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
du_isSurjection_2140 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_isSurjection_400
      (coe d_from_1806 (coe v2))
      (coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.SplitSurjection.strictlyInverseˡ
d_strictlyInverse'737'_2142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_2142 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'737'_2142 v4 v5 v6
du_strictlyInverse'737'_2142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_2142 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'737'_396
      (coe d_from_1806 (coe v2))
      (coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.SplitSurjection.surjection
d_surjection_2144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> T_Surjection_846
d_surjection_2144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_surjection_2144 v6
du_surjection_2144 :: T_LeftInverse_1792 -> T_Surjection_846
du_surjection_2144 v0 = coe du_surjection_1876 (coe v0)
-- Function.Bundles._.SplitSurjection.to
d_to_2146 :: T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_to_2146 v0 = coe d_to_1804 (coe v0)
-- Function.Bundles._.SplitSurjection.to-cong
d_to'45'cong_2148 ::
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_2148 v0 = coe d_to'45'cong_1808 (coe v0)
-- Function.Bundles._.SplitSurjection.Eq₁._≈_
d__'8776'__2152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2152 = erased
-- Function.Bundles._.SplitSurjection.Eq₁._≉_
d__'8777'__2154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2154 = erased
-- Function.Bundles._.SplitSurjection.Eq₁.Carrier
d_Carrier_2156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> ()
d_Carrier_2156 = erased
-- Function.Bundles._.SplitSurjection.Eq₁.isEquivalence
d_isEquivalence_2158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2158 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2158 v4 v5 v6
du_isEquivalence_2158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2158 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.SplitSurjection.Eq₁.isPartialEquivalence
d_isPartialEquivalence_2160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2160 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2160 v4 v5 v6
du_isPartialEquivalence_2160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2160 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₁.partialSetoid
d_partialSetoid_2162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2162 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2162 v4 v5 v6
du_partialSetoid_2162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2162 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.SplitSurjection.Eq₁.refl
d_refl_2164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_refl_2164 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2164 v4 v5 v6
du_refl_2164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
du_refl_2164 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.SplitSurjection.Eq₁.reflexive
d_reflexive_2166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2166 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2166 v4 v5 v6
du_reflexive_2166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2166 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.SplitSurjection.Eq₁.setoid
d_setoid_2168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2168 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2168 v4 v5 v6
du_setoid_2168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2168 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3)))
-- Function.Bundles._.SplitSurjection.Eq₁.sym
d_sym_2170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2170 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2170 v4 v5 v6
du_sym_2170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2170 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₁.trans
d_trans_2172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2172 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2172 v4 v5 v6
du_trans_2172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2172 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₂._≈_
d__'8776'__2176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2176 = erased
-- Function.Bundles._.SplitSurjection.Eq₂._≉_
d__'8777'__2178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2178 = erased
-- Function.Bundles._.SplitSurjection.Eq₂.Carrier
d_Carrier_2180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> ()
d_Carrier_2180 = erased
-- Function.Bundles._.SplitSurjection.Eq₂.isEquivalence
d_isEquivalence_2182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2182 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2182 v4 v5 v6
du_isEquivalence_2182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2182 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.SplitSurjection.Eq₂.isPartialEquivalence
d_isPartialEquivalence_2184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2184 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2184 v4 v5 v6
du_isPartialEquivalence_2184 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2184 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₂.partialSetoid
d_partialSetoid_2186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2186 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2186 v4 v5 v6
du_partialSetoid_2186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2186 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4))))
-- Function.Bundles._.SplitSurjection.Eq₂.refl
d_refl_2188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
d_refl_2188 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2188 v4 v5 v6
du_refl_2188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny
du_refl_2188 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.SplitSurjection.Eq₂.reflexive
d_reflexive_2190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2190 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2190 v4 v5 v6
du_reflexive_2190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2190 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v5))
                 v6)))
-- Function.Bundles._.SplitSurjection.Eq₂.setoid
d_setoid_2192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_2192 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2192 v4 v5 v6
du_setoid_2192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_2192 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_66
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3)))
-- Function.Bundles._.SplitSurjection.Eq₂.sym
d_sym_2194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2194 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2194 v4 v5 v6
du_sym_2194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2194 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₂.trans
d_trans_2196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2196 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2196 v4 v5 v6
du_trans_2196 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  T_LeftInverse_1792 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2196 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1816 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v5)))))
-- Function.Bundles._⟶ₛ_
d__'10230''8347'__2198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 -> ()
d__'10230''8347'__2198 = erased
-- Function.Bundles._⟶_
d__'10230'__2200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'10230'__2200 = erased
-- Function.Bundles._↣_
d__'8611'__2206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8611'__2206 = erased
-- Function.Bundles._↠_
d__'8608'__2212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8608'__2212 = erased
-- Function.Bundles._⤖_
d__'10518'__2218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'10518'__2218 = erased
-- Function.Bundles._⇔_
d__'8660'__2224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8660'__2224 = erased
-- Function.Bundles._↩_
d__'8617'__2230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8617'__2230 = erased
-- Function.Bundles._↪_
d__'8618'__2236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8618'__2236 = erased
-- Function.Bundles._↩↪_
d__'8617''8618'__2242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8617''8618'__2242 = erased
-- Function.Bundles._↔_
d__'8596'__2248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8596'__2248 = erased
-- Function.Bundles._.mk⟶
d_mk'10230'_2266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> T_Func_714
d_mk'10230'_2266 ~v0 ~v1 ~v2 ~v3 v4 = du_mk'10230'_2266 v4
du_mk'10230'_2266 :: (AgdaAny -> AgdaAny) -> T_Func_714
du_mk'10230'_2266 v0
  = coe C_Func'46'constructor_6307 (coe v0) erased
-- Function.Bundles._.mk↣
d_mk'8611'_2272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_Injection_776
d_mk'8611'_2272 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mk'8611'_2272 v4 v5
du_mk'8611'_2272 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_Injection_776
du_mk'8611'_2272 v0 v1
  = coe C_Injection'46'constructor_8675 (coe v0) erased (coe v1)
-- Function.Bundles._.mk↠
d_mk'8608'_2280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Surjection_846
d_mk'8608'_2280 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mk'8608'_2280 v4 v5
du_mk'8608'_2280 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Surjection_846
du_mk'8608'_2280 v0 v1
  = coe C_Surjection'46'constructor_11197 (coe v0) erased (coe v1)
-- Function.Bundles._.mk⤖
d_mk'10518'_2288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Bijection_926
d_mk'10518'_2288 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mk'10518'_2288 v4 v5
du_mk'10518'_2288 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Bijection_926
du_mk'10518'_2288 v0 v1
  = coe C_Bijection'46'constructor_15277 (coe v0) erased (coe v1)
-- Function.Bundles._.mk⇔
d_mk'8660'_2298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Equivalence_1714
d_mk'8660'_2298 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mk'8660'_2298 v4 v5
du_mk'8660'_2298 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Equivalence_1714
du_mk'8660'_2298 v0 v1
  = coe
      C_Equivalence'46'constructor_25797 (coe v0) (coe v1) erased erased
-- Function.Bundles._.mk↩
d_mk'8617'_2308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_LeftInverse_1792
d_mk'8617'_2308 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_mk'8617'_2308 v4 v5 v6
du_mk'8617'_2308 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_LeftInverse_1792
du_mk'8617'_2308 v0 v1 v2
  = coe
      C_LeftInverse'46'constructor_29775 (coe v0) (coe v1) erased erased
      (coe v2)
-- Function.Bundles._.mk↪
d_mk'8618'_2320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_RightInverse_1880
d_mk'8618'_2320 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_mk'8618'_2320 v4 v5 v6
du_mk'8618'_2320 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_RightInverse_1880
du_mk'8618'_2320 v0 v1 v2
  = coe
      C_RightInverse'46'constructor_34573 (coe v0) (coe v1) erased erased
      (coe v2)
-- Function.Bundles._.mk↩↪
d_mk'8617''8618'_2334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_BiInverse_2080
d_mk'8617''8618'_2334 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_mk'8617''8618'_2334 v4 v5 v6 v7 v8
du_mk'8617''8618'_2334 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_BiInverse_2080
du_mk'8617''8618'_2334 v0 v1 v2 v3 v4
  = coe
      C_BiInverse'46'constructor_47439 (coe v0) (coe v1) (coe v2) erased
      erased erased (coe v3) (coe v4)
-- Function.Bundles._.mk↔
d_mk'8596'_2350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Inverse_1960
d_mk'8596'_2350 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_mk'8596'_2350 v4 v5 v6
du_mk'8596'_2350 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Inverse_1960
du_mk'8596'_2350 v0 v1 v2
  = coe
      C_Inverse'46'constructor_38621 (coe v0) (coe v1) erased erased
      (coe v2)
-- Function.Bundles._.mk↠ₛ
d_mk'8608''8347'_2360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Surjection_846
d_mk'8608''8347'_2360 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_mk'8608''8347'_2360 v4 v5
du_mk'8608''8347'_2360 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Surjection_846
du_mk'8608''8347'_2360 v0 v1
  = coe
      du_mk'8608'_2280 (coe v0)
      (coe
         MAlonzo.Code.Function.Consequences.Propositional.du_strictlySurjective'8658'surjective_40
         v0 v1)
-- Function.Bundles._.mk↔ₛ′
d_mk'8596''8347''8242'_2366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_Inverse_1960
d_mk'8596''8347''8242'_2366 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_mk'8596''8347''8242'_2366 v4 v5
du_mk'8596''8347''8242'_2366 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Inverse_1960
du_mk'8596''8347''8242'_2366 v0 v1
  = coe
      du_mk'8596'_2350 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Function.Bundles._._⟨$⟩_
d__'10216''36''10217'__2392 :: T_Func_714 -> AgdaAny -> AgdaAny
d__'10216''36''10217'__2392 v0 = coe d_to_720 (coe v0)
