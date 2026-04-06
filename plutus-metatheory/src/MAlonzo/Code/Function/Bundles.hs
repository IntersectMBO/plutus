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

module MAlonzo.Code.Function.Bundles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Consequences.Propositional
import qualified MAlonzo.Code.Function.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles.Raw
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Function.Bundles._._._≈_
d__'8776'__30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__30 = erased
-- Function.Bundles._._.Carrier
d_Carrier_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 -> ()
d_Carrier_32 = erased
-- Function.Bundles._._.IsBijection
d_IsBijection_50 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsCongruent
d_IsCongruent_54 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsInjection
d_IsInjection_58 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsSurjection
d_IsSurjection_78 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsBijection.isInjection
d_isInjection_232 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
d_isInjection_232 v0
  = coe MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0)
-- Function.Bundles._._.IsBijection.surjective
d_surjective_238 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_238 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_266 (coe v0)
-- Function.Bundles._._.IsBijection.Eq₁._≈_
d__'8776'__242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__242 = erased
-- Function.Bundles._._.IsBijection.Eq₁._≉_
d__'8777'__244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__244 = erased
-- Function.Bundles._._.IsBijection.Eq₁.Carrier
d_Carrier_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 -> ()
d_Carrier_246 = erased
-- Function.Bundles._._.IsBijection.Eq₁.isEquivalence
d_isEquivalence_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_248 v7
du_isEquivalence_248 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_248 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v2)))
-- Function.Bundles._._.IsBijection.Eq₁.isPartialEquivalence
d_isPartialEquivalence_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_250 v7
du_isPartialEquivalence_250 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_250 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₁.partialSetoid
d_partialSetoid_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_252 v7
du_partialSetoid_252 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_252 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2))))
-- Function.Bundles._._.IsBijection.Eq₁.rawSetoid
d_rawSetoid_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_254 = erased
-- Function.Bundles._._.IsBijection.Eq₁.refl
d_refl_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny
d_refl_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_256 v7
du_refl_256 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny
du_refl_256 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v2))))
-- Function.Bundles._._.IsBijection.Eq₁.reflexive
d_reflexive_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_258 v7
du_reflexive_258 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_258 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v3))
                 v4)))
-- Function.Bundles._._.IsBijection.Eq₁.setoid
d_setoid_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_260 v7
du_setoid_260 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_260 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1)))
-- Function.Bundles._._.IsBijection.Eq₁.sym
d_sym_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_262 v7
du_sym_262 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_262 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₁.trans
d_trans_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_264 v7
du_trans_264 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_264 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₂._≈_
d__'8776'__268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__268 = erased
-- Function.Bundles._._.IsBijection.Eq₂._≉_
d__'8777'__270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__270 = erased
-- Function.Bundles._._.IsBijection.Eq₂.Carrier
d_Carrier_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 -> ()
d_Carrier_272 = erased
-- Function.Bundles._._.IsBijection.Eq₂.isEquivalence
d_isEquivalence_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_274 v7
du_isEquivalence_274 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_274 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v2)))
-- Function.Bundles._._.IsBijection.Eq₂.isPartialEquivalence
d_isPartialEquivalence_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_276 v7
du_isPartialEquivalence_276 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_276 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₂.partialSetoid
d_partialSetoid_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_278 v7
du_partialSetoid_278 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_278 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2))))
-- Function.Bundles._._.IsBijection.Eq₂.rawSetoid
d_rawSetoid_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_280 = erased
-- Function.Bundles._._.IsBijection.Eq₂.refl
d_refl_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny
d_refl_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_282 v7
du_refl_282 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny
du_refl_282 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v2))))
-- Function.Bundles._._.IsBijection.Eq₂.reflexive
d_reflexive_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_284 v7
du_reflexive_284 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_284 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v3))
                 v4)))
-- Function.Bundles._._.IsBijection.Eq₂.setoid
d_setoid_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_setoid_286 v7
du_setoid_286 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_286 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_68
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1)))
-- Function.Bundles._._.IsBijection.Eq₂.sym
d_sym_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_288 v7
du_sym_288 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_288 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsBijection.Eq₂.trans
d_trans_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_290 v7
du_trans_290 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_290 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsCongruent.cong
d_cong_294 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_294 v0
  = coe MAlonzo.Code.Function.Structures.d_cong_32 (coe v0)
-- Function.Bundles._._.IsCongruent.isEquivalence₁
d_isEquivalence'8321'_296 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence'8321'_296 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Bundles._._.IsCongruent.isEquivalence₂
d_isEquivalence'8322'_298 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence'8322'_298 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Bundles._._.IsCongruent.Eq₁._≈_
d__'8776'__302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__302 = erased
-- Function.Bundles._._.IsCongruent.Eq₁._≉_
d__'8777'__304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__304 = erased
-- Function.Bundles._._.IsCongruent.Eq₁.Carrier
d_Carrier_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 -> ()
d_Carrier_306 = erased
-- Function.Bundles._._.IsCongruent.Eq₁.isEquivalence
d_isEquivalence_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_308 v7
du_isEquivalence_308 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_308 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Bundles._._.IsCongruent.Eq₁.isPartialEquivalence
d_isPartialEquivalence_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_310 v7
du_isPartialEquivalence_310 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_310 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₁.partialSetoid
d_partialSetoid_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_312 v7
du_partialSetoid_312 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_312 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
      (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0))
-- Function.Bundles._._.IsCongruent.Eq₁.rawSetoid
d_rawSetoid_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_314 = erased
-- Function.Bundles._._.IsCongruent.Eq₁.refl
d_refl_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
d_refl_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_316 v7
du_refl_316 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
du_refl_316 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0))
-- Function.Bundles._._.IsCongruent.Eq₁.reflexive
d_reflexive_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_318 v7
du_reflexive_318 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_318 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
           v2)
-- Function.Bundles._._.IsCongruent.Eq₁.setoid
d_setoid_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_setoid_320
du_setoid_320 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_320 v0 v1
  = coe MAlonzo.Code.Function.Structures.du_setoid_40 v1
-- Function.Bundles._._.IsCongruent.Eq₁.sym
d_sym_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_322 v7
du_sym_322 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_322 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₁.trans
d_trans_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_324 v7
du_trans_324 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_324 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₂._≈_
d__'8776'__328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__328 = erased
-- Function.Bundles._._.IsCongruent.Eq₂._≉_
d__'8777'__330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__330 = erased
-- Function.Bundles._._.IsCongruent.Eq₂.Carrier
d_Carrier_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 -> ()
d_Carrier_332 = erased
-- Function.Bundles._._.IsCongruent.Eq₂.isEquivalence
d_isEquivalence_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isEquivalence_334 v7
du_isEquivalence_334 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_334 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Bundles._._.IsCongruent.Eq₂.isPartialEquivalence
d_isPartialEquivalence_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_336 v7
du_isPartialEquivalence_336 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_336 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₂.partialSetoid
d_partialSetoid_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_partialSetoid_338 v7
du_partialSetoid_338 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_338 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
      (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v0))
-- Function.Bundles._._.IsCongruent.Eq₂.rawSetoid
d_rawSetoid_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_340 = erased
-- Function.Bundles._._.IsCongruent.Eq₂.refl
d_refl_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
d_refl_342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_342 v7
du_refl_342 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
du_refl_342 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0))
-- Function.Bundles._._.IsCongruent.Eq₂.reflexive
d_reflexive_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_344 v7
du_reflexive_344 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_344 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
           v2)
-- Function.Bundles._._.IsCongruent.Eq₂.setoid
d_setoid_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_setoid_346
du_setoid_346 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_346 v0 v1
  = coe MAlonzo.Code.Function.Structures.du_setoid_68 v1
-- Function.Bundles._._.IsCongruent.Eq₂.sym
d_sym_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_sym_348 v7
du_sym_348 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_348 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Function.Bundles._._.IsCongruent.Eq₂.trans
d_trans_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_trans_350 v7
du_trans_350 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_350 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Function.Bundles._._.IsInjection.injective
d_injective_356 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_98 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_356 v0
  = coe MAlonzo.Code.Function.Structures.d_injective_108 (coe v0)
-- Function.Bundles._._.IsInjection.isCongruent
d_isCongruent_358 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_98 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_358 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v0)
-- Function.Bundles._._.IsSurjection.isCongruent
d_isCongruent_712 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_712 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_182 (coe v0)
-- Function.Bundles._._.IsSurjection.strictlySurjective
d_strictlySurjective_718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_strictlySurjective_718
du_strictlySurjective_718 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective_718 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlySurjective_246 v1 v2
-- Function.Bundles._._.IsSurjection.surjective
d_surjective_720 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_720 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_184 (coe v0)
-- Function.Bundles._.Func
d_Func_774 a0 a1 a2 a3 a4 a5 = ()
data T_Func_774
  = C_constructor_840 (AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.Func.to
d_to_780 :: T_Func_774 -> AgdaAny -> AgdaAny
d_to_780 v0
  = case coe v0 of
      C_constructor_840 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Func.cong
d_cong_782 ::
  T_Func_774 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_782 v0
  = case coe v0 of
      C_constructor_840 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Func.isCongruent
d_isCongruent_784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_784 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_784 v4 v5 v6
du_isCongruent_784 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_784 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_94
      (coe d_cong_782 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
-- Function.Bundles._.Func._.Eq₁._≈_
d__'8776'__790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny -> ()
d__'8776'__790 = erased
-- Function.Bundles._.Func._.Eq₁._≉_
d__'8777'__792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny -> ()
d__'8777'__792 = erased
-- Function.Bundles._.Func._.Eq₁.Carrier
d_Carrier_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> ()
d_Carrier_794 = erased
-- Function.Bundles._.Func._.Eq₁.isEquivalence
d_isEquivalence_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_796 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_796 v4 v5 v6
du_isEquivalence_796 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_796 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v3))
-- Function.Bundles._.Func._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_798 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_798 v4 v5 v6
du_isPartialEquivalence_798 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_798 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v4))))
-- Function.Bundles._.Func._.Eq₁.partialSetoid
d_partialSetoid_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_800 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_800 v4 v5 v6
du_partialSetoid_800 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_800 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3)))
-- Function.Bundles._.Func._.Eq₁.rawSetoid
d_rawSetoid_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_802 = erased
-- Function.Bundles._.Func._.Eq₁.refl
d_refl_804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny
d_refl_804 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_804 v4 v5 v6
du_refl_804 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny
du_refl_804 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v3)))
-- Function.Bundles._.Func._.Eq₁.reflexive
d_reflexive_806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_806 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_806 v4 v5 v6
du_reflexive_806 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_806 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3) in
       coe
         (\ v5 v6 v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v4))
              v5))
-- Function.Bundles._.Func._.Eq₁.setoid
d_setoid_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_808 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_808 v4 v5 v6
du_setoid_808 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_808 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe du_isCongruent_784 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.Func._.Eq₁.sym
d_sym_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_810 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_810 v4 v5 v6
du_sym_810 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_810 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v4))))
-- Function.Bundles._.Func._.Eq₁.trans
d_trans_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_812 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_812 v4 v5 v6
du_trans_812 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_812 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v4))))
-- Function.Bundles._.Func._.Eq₂._≈_
d__'8776'__816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny -> ()
d__'8776'__816 = erased
-- Function.Bundles._.Func._.Eq₂._≉_
d__'8777'__818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny -> ()
d__'8777'__818 = erased
-- Function.Bundles._.Func._.Eq₂.Carrier
d_Carrier_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> ()
d_Carrier_820 = erased
-- Function.Bundles._.Func._.Eq₂.isEquivalence
d_isEquivalence_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_822 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_822 v4 v5 v6
du_isEquivalence_822 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_822 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v3))
-- Function.Bundles._.Func._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_824 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_824 v4 v5 v6
du_isPartialEquivalence_824 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_824 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v4))))
-- Function.Bundles._.Func._.Eq₂.partialSetoid
d_partialSetoid_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_826 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_826 v4 v5 v6
du_partialSetoid_826 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_826 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
         (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v3)))
-- Function.Bundles._.Func._.Eq₂.rawSetoid
d_rawSetoid_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_828 = erased
-- Function.Bundles._.Func._.Eq₂.refl
d_refl_830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny
d_refl_830 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_830 v4 v5 v6
du_refl_830 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny
du_refl_830 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v3)))
-- Function.Bundles._.Func._.Eq₂.reflexive
d_reflexive_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_832 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_832 v4 v5 v6
du_reflexive_832 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_832 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v3) in
       coe
         (\ v5 v6 v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v4))
              v5))
-- Function.Bundles._.Func._.Eq₂.setoid
d_setoid_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_834 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_834 v4 v5 v6
du_setoid_834 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_834 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_68
      (coe du_isCongruent_784 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.Func._.Eq₂.sym
d_sym_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_836 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_836 v4 v5 v6
du_sym_836 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_836 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v4))))
-- Function.Bundles._.Func._.Eq₂.trans
d_trans_838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_838 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_838 v4 v5 v6
du_trans_838 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Func_774 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_838 v0 v1 v2
  = let v3 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v4))))
-- Function.Bundles._.Injection
d_Injection_842 a0 a1 a2 a3 a4 a5 = ()
data T_Injection_842
  = C_constructor_916 (AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.Injection.to
d_to_850 :: T_Injection_842 -> AgdaAny -> AgdaAny
d_to_850 v0
  = case coe v0 of
      C_constructor_916 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Injection.cong
d_cong_852 ::
  T_Injection_842 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_852 v0
  = case coe v0 of
      C_constructor_916 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Injection.injective
d_injective_854 ::
  T_Injection_842 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_854 v0
  = case coe v0 of
      C_constructor_916 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Injection.function
d_function_856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> T_Func_774
d_function_856 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_function_856 v6
du_function_856 :: T_Injection_842 -> T_Func_774
du_function_856 v0
  = coe
      C_constructor_840 (coe d_to_850 (coe v0)) (coe d_cong_852 (coe v0))
-- Function.Bundles._.Injection._.isCongruent
d_isCongruent_860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_860 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_860 v4 v5 v6
du_isCongruent_860 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_860 v0 v1 v2
  = coe
      du_isCongruent_784 (coe v0) (coe v1) (coe du_function_856 (coe v2))
-- Function.Bundles._.Injection._.Eq₁._≈_
d__'8776'__864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny -> ()
d__'8776'__864 = erased
-- Function.Bundles._.Injection._.Eq₁._≉_
d__'8777'__866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny -> ()
d__'8777'__866 = erased
-- Function.Bundles._.Injection._.Eq₁.Carrier
d_Carrier_868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> ()
d_Carrier_868 = erased
-- Function.Bundles._.Injection._.Eq₁.isEquivalence
d_isEquivalence_870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_870 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_870 v4 v5 v6
du_isEquivalence_870 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_870 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.Injection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_872 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_872 v4 v5 v6
du_isPartialEquivalence_872 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_872 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₁.partialSetoid
d_partialSetoid_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_874 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_874 v4 v5 v6
du_partialSetoid_874 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_874 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.Injection._.Eq₁.rawSetoid
d_rawSetoid_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_876 = erased
-- Function.Bundles._.Injection._.Eq₁.refl
d_refl_878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny
d_refl_878 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_878 v4 v5 v6
du_refl_878 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny
du_refl_878 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.Injection._.Eq₁.reflexive
d_reflexive_880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_880 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_880 v4 v5 v6
du_reflexive_880 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_880 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.Injection._.Eq₁.setoid
d_setoid_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_882 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_882 v4 v5 v6
du_setoid_882 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_882 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe du_isCongruent_784 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Injection._.Eq₁.sym
d_sym_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_884 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_884 v4 v5 v6
du_sym_884 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_884 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₁.trans
d_trans_886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_886 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_886 v4 v5 v6
du_trans_886 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_886 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₂._≈_
d__'8776'__890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny -> ()
d__'8776'__890 = erased
-- Function.Bundles._.Injection._.Eq₂._≉_
d__'8777'__892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny -> ()
d__'8777'__892 = erased
-- Function.Bundles._.Injection._.Eq₂.Carrier
d_Carrier_894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> ()
d_Carrier_894 = erased
-- Function.Bundles._.Injection._.Eq₂.isEquivalence
d_isEquivalence_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_896 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_896 v4 v5 v6
du_isEquivalence_896 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_896 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.Injection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_898 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_898 v4 v5 v6
du_isPartialEquivalence_898 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_898 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₂.partialSetoid
d_partialSetoid_900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_900 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_900 v4 v5 v6
du_partialSetoid_900 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_900 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4))))
-- Function.Bundles._.Injection._.Eq₂.rawSetoid
d_rawSetoid_902 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_902 = erased
-- Function.Bundles._.Injection._.Eq₂.refl
d_refl_904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny
d_refl_904 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_904 v4 v5 v6
du_refl_904 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny
du_refl_904 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.Injection._.Eq₂.reflexive
d_reflexive_906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_906 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_906 v4 v5 v6
du_reflexive_906 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_906 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.Injection._.Eq₂.setoid
d_setoid_908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_908 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_908 v4 v5 v6
du_setoid_908 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_908 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_68
         (coe du_isCongruent_784 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Injection._.Eq₂.sym
d_sym_910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_910 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_910 v4 v5 v6
du_sym_910 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_910 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Injection._.Eq₂.trans
d_trans_912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_912 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_912 v4 v5 v6
du_trans_912 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_912 v0 v1 v2
  = let v3 = coe du_function_856 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Injection.isInjection
d_isInjection_914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
d_isInjection_914 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isInjection_914 v4 v5 v6
du_isInjection_914 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Injection_842 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
du_isInjection_914 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_170
      (coe
         du_isCongruent_784 (coe v0) (coe v1)
         (coe du_function_856 (coe v2)))
      (coe d_injective_854 (coe v2))
-- Function.Bundles._.Surjection
d_Surjection_918 a0 a1 a2 a3 a4 a5 = ()
data T_Surjection_918
  = C_constructor_1002 (AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Function.Bundles._.Surjection.to
d_to_926 :: T_Surjection_918 -> AgdaAny -> AgdaAny
d_to_926 v0
  = case coe v0 of
      C_constructor_1002 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Surjection.cong
d_cong_928 ::
  T_Surjection_918 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_928 v0
  = case coe v0 of
      C_constructor_1002 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Surjection.surjective
d_surjective_930 ::
  T_Surjection_918 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_930 v0
  = case coe v0 of
      C_constructor_1002 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Surjection.function
d_function_932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> T_Func_774
d_function_932 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_function_932 v6
du_function_932 :: T_Surjection_918 -> T_Func_774
du_function_932 v0
  = coe
      C_constructor_840 (coe d_to_926 (coe v0)) (coe d_cong_928 (coe v0))
-- Function.Bundles._.Surjection._.isCongruent
d_isCongruent_936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_936 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_936 v4 v5 v6
du_isCongruent_936 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_936 v0 v1 v2
  = coe
      du_isCongruent_784 (coe v0) (coe v1) (coe du_function_932 (coe v2))
-- Function.Bundles._.Surjection._.Eq₁._≈_
d__'8776'__940 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny -> ()
d__'8776'__940 = erased
-- Function.Bundles._.Surjection._.Eq₁._≉_
d__'8777'__942 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny -> ()
d__'8777'__942 = erased
-- Function.Bundles._.Surjection._.Eq₁.Carrier
d_Carrier_944 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> ()
d_Carrier_944 = erased
-- Function.Bundles._.Surjection._.Eq₁.isEquivalence
d_isEquivalence_946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_946 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_946 v4 v5 v6
du_isEquivalence_946 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_946 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.Surjection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_948 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_948 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_948 v4 v5 v6
du_isPartialEquivalence_948 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_948 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₁.partialSetoid
d_partialSetoid_950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_950 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_950 v4 v5 v6
du_partialSetoid_950 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_950 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.Surjection._.Eq₁.rawSetoid
d_rawSetoid_952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_952 = erased
-- Function.Bundles._.Surjection._.Eq₁.refl
d_refl_954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny
d_refl_954 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_954 v4 v5 v6
du_refl_954 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny
du_refl_954 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.Surjection._.Eq₁.reflexive
d_reflexive_956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_956 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_956 v4 v5 v6
du_reflexive_956 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_956 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.Surjection._.Eq₁.setoid
d_setoid_958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_958 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_958 v4 v5 v6
du_setoid_958 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_958 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe du_isCongruent_784 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Surjection._.Eq₁.sym
d_sym_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_960 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_960 v4 v5 v6
du_sym_960 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_960 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₁.trans
d_trans_962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_962 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_962 v4 v5 v6
du_trans_962 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_962 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₂._≈_
d__'8776'__966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny -> ()
d__'8776'__966 = erased
-- Function.Bundles._.Surjection._.Eq₂._≉_
d__'8777'__968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny -> ()
d__'8777'__968 = erased
-- Function.Bundles._.Surjection._.Eq₂.Carrier
d_Carrier_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> ()
d_Carrier_970 = erased
-- Function.Bundles._.Surjection._.Eq₂.isEquivalence
d_isEquivalence_972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_972 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_972 v4 v5 v6
du_isEquivalence_972 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_972 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.Surjection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_974 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_974 v4 v5 v6
du_isPartialEquivalence_974 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_974 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₂.partialSetoid
d_partialSetoid_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_976 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_976 v4 v5 v6
du_partialSetoid_976 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_976 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4))))
-- Function.Bundles._.Surjection._.Eq₂.rawSetoid
d_rawSetoid_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_978 = erased
-- Function.Bundles._.Surjection._.Eq₂.refl
d_refl_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny
d_refl_980 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_980 v4 v5 v6
du_refl_980 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny
du_refl_980 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.Surjection._.Eq₂.reflexive
d_reflexive_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_982 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_982 v4 v5 v6
du_reflexive_982 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_982 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.Surjection._.Eq₂.setoid
d_setoid_984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_984 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_984 v4 v5 v6
du_setoid_984 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_984 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_68
         (coe du_isCongruent_784 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Surjection._.Eq₂.sym
d_sym_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_986 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_986 v4 v5 v6
du_sym_986 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_986 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Surjection._.Eq₂.trans
d_trans_988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_988 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_988 v4 v5 v6
du_trans_988 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_988 v0 v1 v2
  = let v3 = coe du_function_932 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Surjection.isSurjection
d_isSurjection_990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
d_isSurjection_990 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSurjection_990 v4 v5 v6
du_isSurjection_990 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
du_isSurjection_990 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_252
      (coe
         du_isCongruent_784 (coe v0) (coe v1)
         (coe du_function_932 (coe v2)))
      (coe d_surjective_930 (coe v2))
-- Function.Bundles._.Surjection._.strictlySurjective
d_strictlySurjective_994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_994 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlySurjective_994 v4 v5 v6
du_strictlySurjective_994 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective_994 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlySurjective_246
      (coe du_isSurjection_990 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.Surjection.to⁻
d_to'8315'_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny
d_to'8315'_996 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_to'8315'_996 v6 v7
du_to'8315'_996 :: T_Surjection_918 -> AgdaAny -> AgdaAny
du_to'8315'_996 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_surjective_930 v0 v1)
-- Function.Bundles._.Surjection.to∘to⁻
d_to'8728'to'8315'_1000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny
d_to'8728'to'8315'_1000 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_to'8728'to'8315'_1000 v4 v5 v6 v7
du_to'8728'to'8315'_1000 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Surjection_918 -> AgdaAny -> AgdaAny
du_to'8728'to'8315'_1000 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Function.Structures.du_strictlySurjective_246
         (coe du_isSurjection_990 (coe v0) (coe v1) (coe v2)) (coe v3))
-- Function.Bundles._.Bijection
d_Bijection_1004 a0 a1 a2 a3 a4 a5 = ()
data T_Bijection_1004
  = C_constructor_1094 (AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Function.Bundles._.Bijection.to
d_to_1012 :: T_Bijection_1004 -> AgdaAny -> AgdaAny
d_to_1012 v0
  = case coe v0 of
      C_constructor_1094 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Bijection.cong
d_cong_1014 ::
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1014 v0
  = case coe v0 of
      C_constructor_1094 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Bijection.bijective
d_bijective_1016 ::
  T_Bijection_1004 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bijective_1016 v0
  = case coe v0 of
      C_constructor_1094 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Bijection.injective
d_injective_1018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_1018 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_injective_1018 v6 v7 v8
du_injective_1018 ::
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_injective_1018 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (d_bijective_1016 (coe v0)) v1 v2
-- Function.Bundles._.Bijection.surjective
d_surjective_1020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_1020 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_surjective_1020 v6
du_surjective_1020 ::
  T_Bijection_1004 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_surjective_1020 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_bijective_1016 (coe v0))
-- Function.Bundles._.Bijection.injection
d_injection_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> T_Injection_842
d_injection_1022 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_injection_1022 v6
du_injection_1022 :: T_Bijection_1004 -> T_Injection_842
du_injection_1022 v0
  = coe
      C_constructor_916 (coe d_to_1012 (coe v0))
      (coe d_cong_1014 (coe v0)) (coe du_injective_1018 (coe v0))
-- Function.Bundles._.Bijection.surjection
d_surjection_1024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> T_Surjection_918
d_surjection_1024 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_surjection_1024 v6
du_surjection_1024 :: T_Bijection_1004 -> T_Surjection_918
du_surjection_1024 v0
  = coe
      C_constructor_1002 (coe d_to_1012 (coe v0))
      (coe d_cong_1014 (coe v0)) (coe du_surjective_1020 (coe v0))
-- Function.Bundles._.Bijection._.isInjection
d_isInjection_1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
d_isInjection_1028 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isInjection_1028 v4 v5 v6
du_isInjection_1028 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
du_isInjection_1028 v0 v1 v2
  = coe
      du_isInjection_914 (coe v0) (coe v1)
      (coe du_injection_1022 (coe v2))
-- Function.Bundles._.Bijection._.isSurjection
d_isSurjection_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
d_isSurjection_1032 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSurjection_1032 v4 v5 v6
du_isSurjection_1032 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
du_isSurjection_1032 v0 v1 v2
  = coe
      du_isSurjection_990 (coe v0) (coe v1)
      (coe du_surjection_1024 (coe v2))
-- Function.Bundles._.Bijection._.strictlySurjective
d_strictlySurjective_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_1034 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlySurjective_1034 v4 v5 v6
du_strictlySurjective_1034 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective_1034 v0 v1 v2
  = let v3 = coe du_surjection_1024 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_strictlySurjective_246
         (coe du_isSurjection_990 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Bijection._.to⁻
d_to'8315'_1036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny
d_to'8315'_1036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_to'8315'_1036 v6
du_to'8315'_1036 :: T_Bijection_1004 -> AgdaAny -> AgdaAny
du_to'8315'_1036 v0
  = coe du_to'8315'_996 (coe du_surjection_1024 (coe v0))
-- Function.Bundles._.Bijection.isBijection
d_isBijection_1038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256
d_isBijection_1038 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isBijection_1038 v4 v5 v6
du_isBijection_1038 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256
du_isBijection_1038 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_340
      (coe
         du_isInjection_914 (coe v0) (coe v1)
         (coe du_injection_1022 (coe v2)))
      (coe du_surjective_1020 (coe v2))
-- Function.Bundles._.Bijection._.Eq₁._≈_
d__'8776'__1044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1044 = erased
-- Function.Bundles._.Bijection._.Eq₁._≉_
d__'8777'__1046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1046 = erased
-- Function.Bundles._.Bijection._.Eq₁.Carrier
d_Carrier_1048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> ()
d_Carrier_1048 = erased
-- Function.Bundles._.Bijection._.Eq₁.isEquivalence
d_isEquivalence_1050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1050 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1050 v4 v5 v6
du_isEquivalence_1050 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1050 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v5))))
-- Function.Bundles._.Bijection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1052 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1052 v4 v5 v6
du_isPartialEquivalence_1052 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1052 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₁.partialSetoid
d_partialSetoid_1054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1054 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1054 v4 v5 v6
du_partialSetoid_1054 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1054 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
               (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5)))))
-- Function.Bundles._.Bijection._.Eq₁.rawSetoid
d_rawSetoid_1056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1056 = erased
-- Function.Bundles._.Bijection._.Eq₁.refl
d_refl_1058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny
d_refl_1058 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1058 v4 v5 v6
du_refl_1058 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny
du_refl_1058 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
                  (coe v5)))))
-- Function.Bundles._.Bijection._.Eq₁.reflexive
d_reflexive_1060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1060 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1060 v4 v5 v6
du_reflexive_1060 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1060 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (\ v7 v8 v9 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v6))
                    v7))))
-- Function.Bundles._.Bijection._.Eq₁.setoid
d_setoid_1062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1062 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1062 v4 v5 v6
du_setoid_1062 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1062 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_40
            (coe MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4))))
-- Function.Bundles._.Bijection._.Eq₁.sym
d_sym_1064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1064 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1064 v4 v5 v6
du_sym_1064 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1064 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₁.trans
d_trans_1066 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1066 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1066 v4 v5 v6
du_trans_1066 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1066 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₂._≈_
d__'8776'__1070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1070 = erased
-- Function.Bundles._.Bijection._.Eq₂._≉_
d__'8777'__1072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1072 = erased
-- Function.Bundles._.Bijection._.Eq₂.Carrier
d_Carrier_1074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> ()
d_Carrier_1074 = erased
-- Function.Bundles._.Bijection._.Eq₂.isEquivalence
d_isEquivalence_1076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1076 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1076 v4 v5 v6
du_isEquivalence_1076 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1076 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v5))))
-- Function.Bundles._.Bijection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1078 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1078 v4 v5 v6
du_isPartialEquivalence_1078 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1078 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₂.partialSetoid
d_partialSetoid_1080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1080 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1080 v4 v5 v6
du_partialSetoid_1080 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1080 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
               (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5)))))
-- Function.Bundles._.Bijection._.Eq₂.rawSetoid
d_rawSetoid_1082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1082 = erased
-- Function.Bundles._.Bijection._.Eq₂.refl
d_refl_1084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny
d_refl_1084 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1084 v4 v5 v6
du_refl_1084 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny
du_refl_1084 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
                  (coe v5)))))
-- Function.Bundles._.Bijection._.Eq₂.reflexive
d_reflexive_1086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1086 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1086 v4 v5 v6
du_reflexive_1086 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1086 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5) in
             coe
               (\ v7 v8 v9 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v6))
                    v7))))
-- Function.Bundles._.Bijection._.Eq₂.setoid
d_setoid_1088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1088 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1088 v4 v5 v6
du_setoid_1088 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1088 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_68
            (coe MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4))))
-- Function.Bundles._.Bijection._.Eq₂.sym
d_sym_1090 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1090 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1090 v4 v5 v6
du_sym_1090 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1090 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Bijection._.Eq₂.trans
d_trans_1092 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1092 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1092 v4 v5 v6
du_trans_1092 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Bijection_1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1092 v0 v1 v2
  = let v3 = coe du_isBijection_1038 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._._._≈_
d__'8776'__1114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1114 = erased
-- Function.Bundles._._.Carrier
d_Carrier_1116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 -> ()
d_Carrier_1116 = erased
-- Function.Bundles._._.IsBiInverse
d_IsBiInverse_1130 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Function.Bundles._._.IsCongruent
d_IsCongruent_1138 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsInverse
d_IsInverse_1146 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Function.Bundles._._.IsLeftInverse
d_IsLeftInverse_1150 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Function.Bundles._._.IsRightInverse
d_IsRightInverse_1154 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Function.Bundles._._.IsSplitSurjection
d_IsSplitSurjection_1158 a0 a1 a2 a3 a4 a5 a6 = ()
-- Function.Bundles._._.IsBiInverse.from₁-cong
d_from'8321''45'cong_1234 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8321''45'cong_1234 v0
  = coe
      MAlonzo.Code.Function.Structures.d_from'8321''45'cong_734 (coe v0)
-- Function.Bundles._._.IsBiInverse.from₂-cong
d_from'8322''45'cong_1236 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8322''45'cong_1236 v0
  = coe
      MAlonzo.Code.Function.Structures.d_from'8322''45'cong_736 (coe v0)
-- Function.Bundles._._.IsBiInverse.inverseʳ
d_inverse'691'_1238 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_1238 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_740 (coe v0)
-- Function.Bundles._._.IsBiInverse.inverseˡ
d_inverse'737'_1240 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_714 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_1240 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'737'_738 (coe v0)
-- Function.Bundles._._.IsBiInverse.to-isCongruent
d_to'45'isCongruent_1248 ::
  MAlonzo.Code.Function.Structures.T_IsBiInverse_714 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_to'45'isCongruent_1248 v0
  = coe
      MAlonzo.Code.Function.Structures.d_to'45'isCongruent_732 (coe v0)
-- Function.Bundles._._.IsCongruent.cong
d_cong_1378 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_1378 v0
  = coe MAlonzo.Code.Function.Structures.d_cong_32 (coe v0)
-- Function.Bundles._._.IsCongruent.isEquivalence₁
d_isEquivalence'8321'_1380 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence'8321'_1380 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Bundles._._.IsCongruent.isEquivalence₂
d_isEquivalence'8322'_1382 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence'8322'_1382 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Bundles._._.IsInverse.inverseʳ
d_inverse'691'_1506 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_1506 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_538 (coe v0)
-- Function.Bundles._._.IsInverse.isLeftInverse
d_isLeftInverse_1516 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
d_isLeftInverse_1516 v0
  = coe MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0)
-- Function.Bundles._._.IsInverse.Eq₁._≈_
d__'8776'__1530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1530 = erased
-- Function.Bundles._._.IsInverse.Eq₁._≉_
d__'8777'__1532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1532 = erased
-- Function.Bundles._._.IsInverse.Eq₁.Carrier
d_Carrier_1534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 -> ()
d_Carrier_1534 = erased
-- Function.Bundles._._.IsInverse.Eq₁.isEquivalence
d_isEquivalence_1536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1536 v8
du_isEquivalence_1536 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1536 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v2)))
-- Function.Bundles._._.IsInverse.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1538 v8
du_isPartialEquivalence_1538 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1538 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₁.partialSetoid
d_partialSetoid_1540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1540 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1540 v8
du_partialSetoid_1540 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1540 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2))))
-- Function.Bundles._._.IsInverse.Eq₁.rawSetoid
d_rawSetoid_1542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1542 = erased
-- Function.Bundles._._.IsInverse.Eq₁.refl
d_refl_1544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny
d_refl_1544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1544 v8
du_refl_1544 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny
du_refl_1544 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v2))))
-- Function.Bundles._._.IsInverse.Eq₁.reflexive
d_reflexive_1546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1546 v8
du_reflexive_1546 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1546 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v3))
                 v4)))
-- Function.Bundles._._.IsInverse.Eq₁.setoid
d_setoid_1548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1548 v8
du_setoid_1548 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1548 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1)))
-- Function.Bundles._._.IsInverse.Eq₁.sym
d_sym_1550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1550 v8
du_sym_1550 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1550 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₁.trans
d_trans_1552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1552 v8
du_trans_1552 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1552 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₂._≈_
d__'8776'__1556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1556 = erased
-- Function.Bundles._._.IsInverse.Eq₂._≉_
d__'8777'__1558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1558 = erased
-- Function.Bundles._._.IsInverse.Eq₂.Carrier
d_Carrier_1560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 -> ()
d_Carrier_1560 = erased
-- Function.Bundles._._.IsInverse.Eq₂.isEquivalence
d_isEquivalence_1562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1562 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1562 v8
du_isEquivalence_1562 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1562 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v2)))
-- Function.Bundles._._.IsInverse.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1564 v8
du_isPartialEquivalence_1564 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1564 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₂.partialSetoid
d_partialSetoid_1566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1566 v8
du_partialSetoid_1566 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1566 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2))))
-- Function.Bundles._._.IsInverse.Eq₂.rawSetoid
d_rawSetoid_1568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1568 = erased
-- Function.Bundles._._.IsInverse.Eq₂.refl
d_refl_1570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny
d_refl_1570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1570 v8
du_refl_1570 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny
du_refl_1570 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v2))))
-- Function.Bundles._._.IsInverse.Eq₂.reflexive
d_reflexive_1572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1572 v8
du_reflexive_1572 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1572 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v3))
                 v4)))
-- Function.Bundles._._.IsInverse.Eq₂.setoid
d_setoid_1574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1574 v8
du_setoid_1574 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1574 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_68
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1)))
-- Function.Bundles._._.IsInverse.Eq₂.sym
d_sym_1576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1576 v8
du_sym_1576 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1576 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsInverse.Eq₂.trans
d_trans_1578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1578 v8
du_trans_1578 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1578 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v3)))))
-- Function.Bundles._._.IsLeftInverse.from-cong
d_from'45'cong_1582 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1582 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_360 (coe v0)
-- Function.Bundles._._.IsLeftInverse.inverseˡ
d_inverse'737'_1584 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_1584 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'737'_362 (coe v0)
-- Function.Bundles._._.IsLeftInverse.isCongruent
d_isCongruent_1586 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1586 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0)
-- Function.Bundles._._.IsLeftInverse.isSurjection
d_isSurjection_1592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
d_isSurjection_1592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_isSurjection_1592
du_isSurjection_1592 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
du_isSurjection_1592 v0 v1 v2
  = coe MAlonzo.Code.Function.Structures.du_isSurjection_428 v1 v2
-- Function.Bundles._._.IsLeftInverse.strictlyInverseˡ
d_strictlyInverse'737'_1594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny
d_strictlyInverse'737'_1594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_strictlyInverse'737'_1594
du_strictlyInverse'737'_1594 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny
du_strictlyInverse'737'_1594 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'737'_424 v1 v2
      v3
-- Function.Bundles._._.IsLeftInverse.Eq₁._≈_
d__'8776'__1600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1600 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₁._≉_
d__'8777'__1602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1602 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₁.Carrier
d_Carrier_1604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 -> ()
d_Carrier_1604 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₁.isEquivalence
d_isEquivalence_1606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1606 v8
du_isEquivalence_1606 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1606 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v1))
-- Function.Bundles._._.IsLeftInverse.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1608 v8
du_isPartialEquivalence_1608 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1608 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₁.partialSetoid
d_partialSetoid_1610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1610 v8
du_partialSetoid_1610 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1610 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1)))
-- Function.Bundles._._.IsLeftInverse.Eq₁.rawSetoid
d_rawSetoid_1612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1612 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₁.refl
d_refl_1614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny
d_refl_1614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1614 v8
du_refl_1614 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny
du_refl_1614 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v1)))
-- Function.Bundles._._.IsLeftInverse.Eq₁.reflexive
d_reflexive_1616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1616 v8
du_reflexive_1616 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1616 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))
              v3))
-- Function.Bundles._._.IsLeftInverse.Eq₁.setoid
d_setoid_1618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1618 v8
du_setoid_1618 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1618 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0))
-- Function.Bundles._._.IsLeftInverse.Eq₁.sym
d_sym_1620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1620 v8
du_sym_1620 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1620 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₁.trans
d_trans_1622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1622 v8
du_trans_1622 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1622 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₂._≈_
d__'8776'__1626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1626 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₂._≉_
d__'8777'__1628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1628 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₂.Carrier
d_Carrier_1630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 -> ()
d_Carrier_1630 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₂.isEquivalence
d_isEquivalence_1632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1632 v8
du_isEquivalence_1632 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1632 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v1))
-- Function.Bundles._._.IsLeftInverse.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1634 v8
du_isPartialEquivalence_1634 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1634 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₂.partialSetoid
d_partialSetoid_1636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1636 v8
du_partialSetoid_1636 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1636 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
         (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1)))
-- Function.Bundles._._.IsLeftInverse.Eq₂.rawSetoid
d_rawSetoid_1638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1638 = erased
-- Function.Bundles._._.IsLeftInverse.Eq₂.refl
d_refl_1640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny
d_refl_1640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1640 v8
du_refl_1640 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny
du_refl_1640 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v1)))
-- Function.Bundles._._.IsLeftInverse.Eq₂.reflexive
d_reflexive_1642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1642 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1642 v8
du_reflexive_1642 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1642 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))
              v3))
-- Function.Bundles._._.IsLeftInverse.Eq₂.setoid
d_setoid_1644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1644 v8
du_setoid_1644 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1644 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_68
      (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0))
-- Function.Bundles._._.IsLeftInverse.Eq₂.sym
d_sym_1646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1646 v8
du_sym_1646 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1646 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsLeftInverse.Eq₂.trans
d_trans_1648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1648 v8
du_trans_1648 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1648 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsRightInverse.from-cong
d_from'45'cong_1652 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1652 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_452 (coe v0)
-- Function.Bundles._._.IsRightInverse.inverseʳ
d_inverse'691'_1654 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_1654 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_454 (coe v0)
-- Function.Bundles._._.IsRightInverse.isCongruent
d_isCongruent_1656 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1656 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0)
-- Function.Bundles._._.IsRightInverse.strictlyInverseʳ
d_strictlyInverse'691'_1662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny
d_strictlyInverse'691'_1662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_strictlyInverse'691'_1662
du_strictlyInverse'691'_1662 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny
du_strictlyInverse'691'_1662 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'691'_516 v0 v2
      v3
-- Function.Bundles._._.IsRightInverse.Eq₁._≈_
d__'8776'__1668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1668 = erased
-- Function.Bundles._._.IsRightInverse.Eq₁._≉_
d__'8777'__1670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1670 = erased
-- Function.Bundles._._.IsRightInverse.Eq₁.Carrier
d_Carrier_1672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 -> ()
d_Carrier_1672 = erased
-- Function.Bundles._._.IsRightInverse.Eq₁.isEquivalence
d_isEquivalence_1674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1674 v8
du_isEquivalence_1674 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1674 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v1))
-- Function.Bundles._._.IsRightInverse.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1676 v8
du_isPartialEquivalence_1676 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1676 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₁.partialSetoid
d_partialSetoid_1678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1678 v8
du_partialSetoid_1678 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1678 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1)))
-- Function.Bundles._._.IsRightInverse.Eq₁.rawSetoid
d_rawSetoid_1680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1680 = erased
-- Function.Bundles._._.IsRightInverse.Eq₁.refl
d_refl_1682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny
d_refl_1682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1682 v8
du_refl_1682 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny
du_refl_1682 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v1)))
-- Function.Bundles._._.IsRightInverse.Eq₁.reflexive
d_reflexive_1684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1684 v8
du_reflexive_1684 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1684 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))
              v3))
-- Function.Bundles._._.IsRightInverse.Eq₁.setoid
d_setoid_1686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1686 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1686 v8
du_setoid_1686 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1686 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0))
-- Function.Bundles._._.IsRightInverse.Eq₁.sym
d_sym_1688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1688 v8
du_sym_1688 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1688 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₁.trans
d_trans_1690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1690 v8
du_trans_1690 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1690 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₂._≈_
d__'8776'__1694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__1694 = erased
-- Function.Bundles._._.IsRightInverse.Eq₂._≉_
d__'8777'__1696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__1696 = erased
-- Function.Bundles._._.IsRightInverse.Eq₂.Carrier
d_Carrier_1698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 -> ()
d_Carrier_1698 = erased
-- Function.Bundles._._.IsRightInverse.Eq₂.isEquivalence
d_isEquivalence_1700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isEquivalence_1700 v8
du_isEquivalence_1700 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1700 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v1))
-- Function.Bundles._._.IsRightInverse.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_1702 v8
du_isPartialEquivalence_1702 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1702 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₂.partialSetoid
d_partialSetoid_1704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_partialSetoid_1704 v8
du_partialSetoid_1704 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1704 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
         (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1)))
-- Function.Bundles._._.IsRightInverse.Eq₂.rawSetoid
d_rawSetoid_1706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1706 = erased
-- Function.Bundles._._.IsRightInverse.Eq₂.refl
d_refl_1708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny
d_refl_1708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_1708 v8
du_refl_1708 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny
du_refl_1708 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v1)))
-- Function.Bundles._._.IsRightInverse.Eq₂.reflexive
d_reflexive_1710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_1710 v8
du_reflexive_1710 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1710 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))
              v3))
-- Function.Bundles._._.IsRightInverse.Eq₂.setoid
d_setoid_1712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_setoid_1712 v8
du_setoid_1712 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1712 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_68
      (coe MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0))
-- Function.Bundles._._.IsRightInverse.Eq₂.sym
d_sym_1714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_sym_1714 v8
du_sym_1714 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1714 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsRightInverse.Eq₂.trans
d_trans_1716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_trans_1716 v8
du_trans_1716 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1716 v0
  = let v1
          = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v2))))
-- Function.Bundles._._.IsSplitSurjection.from
d_from_1720 ::
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_806 ->
  AgdaAny -> AgdaAny
d_from_1720 v0
  = coe MAlonzo.Code.Function.Structures.d_from_814 (coe v0)
-- Function.Bundles._._.IsSplitSurjection.isLeftInverse
d_isLeftInverse_1732 ::
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_806 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
d_isLeftInverse_1732 v0
  = coe MAlonzo.Code.Function.Structures.d_isLeftInverse_816 (coe v0)
-- Function.Bundles._.Equivalence
d_Equivalence_1858 a0 a1 a2 a3 a4 a5 = ()
data T_Equivalence_1858
  = C_constructor_1940 (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.Equivalence.to
d_to_1868 :: T_Equivalence_1858 -> AgdaAny -> AgdaAny
d_to_1868 v0
  = case coe v0 of
      C_constructor_1940 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Equivalence.from
d_from_1870 :: T_Equivalence_1858 -> AgdaAny -> AgdaAny
d_from_1870 v0
  = case coe v0 of
      C_constructor_1940 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Equivalence.to-cong
d_to'45'cong_1872 ::
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_1872 v0
  = case coe v0 of
      C_constructor_1940 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Equivalence.from-cong
d_from'45'cong_1874 ::
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1874 v0
  = case coe v0 of
      C_constructor_1940 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Equivalence.toFunction
d_toFunction_1876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> T_Func_774
d_toFunction_1876 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_toFunction_1876 v6
du_toFunction_1876 :: T_Equivalence_1858 -> T_Func_774
du_toFunction_1876 v0
  = coe
      C_constructor_840 (coe d_to_1868 (coe v0))
      (coe d_to'45'cong_1872 (coe v0))
-- Function.Bundles._.Equivalence._.isCongruent
d_isCongruent_1880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1880 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_1880 v4 v5 v6
du_isCongruent_1880 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_1880 v0 v1 v2
  = coe
      du_isCongruent_784 (coe v0) (coe v1)
      (coe du_toFunction_1876 (coe v2))
-- Function.Bundles._.Equivalence._.Eq₁._≈_
d__'8776'__1884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1884 = erased
-- Function.Bundles._.Equivalence._.Eq₁._≉_
d__'8777'__1886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1886 = erased
-- Function.Bundles._.Equivalence._.Eq₁.Carrier
d_Carrier_1888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> ()
d_Carrier_1888 = erased
-- Function.Bundles._.Equivalence._.Eq₁.isEquivalence
d_isEquivalence_1890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1890 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1890 v4 v5 v6
du_isEquivalence_1890 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1890 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.Equivalence._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1892 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1892 v4 v5 v6
du_isPartialEquivalence_1892 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1892 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₁.partialSetoid
d_partialSetoid_1894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1894 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1894 v4 v5 v6
du_partialSetoid_1894 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1894 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.Equivalence._.Eq₁.rawSetoid
d_rawSetoid_1896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1896 = erased
-- Function.Bundles._.Equivalence._.Eq₁.refl
d_refl_1898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny
d_refl_1898 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1898 v4 v5 v6
du_refl_1898 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny
du_refl_1898 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.Equivalence._.Eq₁.reflexive
d_reflexive_1900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1900 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1900 v4 v5 v6
du_reflexive_1900 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1900 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.Equivalence._.Eq₁.setoid
d_setoid_1902 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1902 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1902 v4 v5 v6
du_setoid_1902 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1902 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe du_isCongruent_784 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Equivalence._.Eq₁.sym
d_sym_1904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1904 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1904 v4 v5 v6
du_sym_1904 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1904 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₁.trans
d_trans_1906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1906 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1906 v4 v5 v6
du_trans_1906 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1906 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₂._≈_
d__'8776'__1910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1910 = erased
-- Function.Bundles._.Equivalence._.Eq₂._≉_
d__'8777'__1912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1912 = erased
-- Function.Bundles._.Equivalence._.Eq₂.Carrier
d_Carrier_1914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> ()
d_Carrier_1914 = erased
-- Function.Bundles._.Equivalence._.Eq₂.isEquivalence
d_isEquivalence_1916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1916 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1916 v4 v5 v6
du_isEquivalence_1916 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1916 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.Equivalence._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1918 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1918 v4 v5 v6
du_isPartialEquivalence_1918 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1918 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₂.partialSetoid
d_partialSetoid_1920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1920 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1920 v4 v5 v6
du_partialSetoid_1920 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1920 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4))))
-- Function.Bundles._.Equivalence._.Eq₂.rawSetoid
d_rawSetoid_1922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1922 = erased
-- Function.Bundles._.Equivalence._.Eq₂.refl
d_refl_1924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny
d_refl_1924 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1924 v4 v5 v6
du_refl_1924 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny
du_refl_1924 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.Equivalence._.Eq₂.reflexive
d_reflexive_1926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1926 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1926 v4 v5 v6
du_reflexive_1926 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1926 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.Equivalence._.Eq₂.setoid
d_setoid_1928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1928 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1928 v4 v5 v6
du_setoid_1928 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1928 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_68
         (coe du_isCongruent_784 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Equivalence._.Eq₂.sym
d_sym_1930 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1930 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1930 v4 v5 v6
du_sym_1930 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1930 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Equivalence._.Eq₂.trans
d_trans_1932 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1932 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1932 v4 v5 v6
du_trans_1932 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1932 v0 v1 v2
  = let v3 = coe du_toFunction_1876 (coe v2) in
    coe
      (let v4 = coe du_isCongruent_784 (coe v0) (coe v1) (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.Equivalence.fromFunction
d_fromFunction_1934 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 -> T_Func_774
d_fromFunction_1934 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_fromFunction_1934 v6
du_fromFunction_1934 :: T_Equivalence_1858 -> T_Func_774
du_fromFunction_1934 v0
  = coe
      C_constructor_840 (coe d_from_1870 (coe v0))
      (coe d_from'45'cong_1874 (coe v0))
-- Function.Bundles._.Equivalence._.isCongruent
d_isCongruent_1938 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1938 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_1938 v4 v5 v6
du_isCongruent_1938 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Equivalence_1858 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_1938 v0 v1 v2
  = coe
      du_isCongruent_784 (coe v1) (coe v0)
      (coe du_fromFunction_1934 (coe v2))
-- Function.Bundles._.LeftInverse
d_LeftInverse_1942 a0 a1 a2 a3 a4 a5 = ()
data T_LeftInverse_1942
  = C_constructor_2034 (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.LeftInverse.to
d_to_1954 :: T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_to_1954 v0
  = case coe v0 of
      C_constructor_2034 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.from
d_from_1956 :: T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_from_1956 v0
  = case coe v0 of
      C_constructor_2034 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.to-cong
d_to'45'cong_1958 ::
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_1958 v0
  = case coe v0 of
      C_constructor_2034 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.from-cong
d_from'45'cong_1960 ::
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_1960 v0
  = case coe v0 of
      C_constructor_2034 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.inverseˡ
d_inverse'737'_1962 ::
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_1962 v0
  = case coe v0 of
      C_constructor_2034 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.LeftInverse.isCongruent
d_isCongruent_1964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_1964 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_1964 v4 v5 v6
du_isCongruent_1964 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_1964 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_94
      (coe d_to'45'cong_1958 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
-- Function.Bundles._.LeftInverse.isLeftInverse
d_isLeftInverse_1966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
d_isLeftInverse_1966 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isLeftInverse_1966 v4 v5 v6
du_isLeftInverse_1966 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
du_isLeftInverse_1966 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_432
      (coe du_isCongruent_1964 (coe v0) (coe v1) (coe v2))
      (coe d_from'45'cong_1960 (coe v2))
      (coe d_inverse'737'_1962 (coe v2))
-- Function.Bundles._.LeftInverse._.isSurjection
d_isSurjection_1970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
d_isSurjection_1970 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSurjection_1970 v4 v5 v6
du_isSurjection_1970 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
du_isSurjection_1970 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_isSurjection_428
      (coe d_from_1956 (coe v2))
      (coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.LeftInverse._.strictlyInverseˡ
d_strictlyInverse'737'_1972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_1972 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'737'_1972 v4 v5 v6
du_strictlyInverse'737'_1972 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_1972 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'737'_424
      (coe d_from_1956 (coe v2))
      (coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.LeftInverse._.Eq₁._≈_
d__'8776'__1976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> ()
d__'8776'__1976 = erased
-- Function.Bundles._.LeftInverse._.Eq₁._≉_
d__'8777'__1978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> ()
d__'8777'__1978 = erased
-- Function.Bundles._.LeftInverse._.Eq₁.Carrier
d_Carrier_1980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> ()
d_Carrier_1980 = erased
-- Function.Bundles._.LeftInverse._.Eq₁.isEquivalence
d_isEquivalence_1982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1982 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_1982 v4 v5 v6
du_isEquivalence_1982 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_1982 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.LeftInverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_1984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1984 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_1984 v4 v5 v6
du_isPartialEquivalence_1984 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1984 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₁.partialSetoid
d_partialSetoid_1986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1986 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_1986 v4 v5 v6
du_partialSetoid_1986 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1986 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.LeftInverse._.Eq₁.rawSetoid
d_rawSetoid_1988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_1988 = erased
-- Function.Bundles._.LeftInverse._.Eq₁.refl
d_refl_1990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_refl_1990 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_1990 v4 v5 v6
du_refl_1990 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
du_refl_1990 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.LeftInverse._.Eq₁.reflexive
d_reflexive_1992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1992 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_1992 v4 v5 v6
du_reflexive_1992 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1992 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.LeftInverse._.Eq₁.setoid
d_setoid_1994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1994 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_1994 v4 v5 v6
du_setoid_1994 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1994 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3)))
-- Function.Bundles._.LeftInverse._.Eq₁.sym
d_sym_1996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1996 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_1996 v4 v5 v6
du_sym_1996 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1996 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₁.trans
d_trans_1998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1998 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_1998 v4 v5 v6
du_trans_1998 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1998 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₂._≈_
d__'8776'__2002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2002 = erased
-- Function.Bundles._.LeftInverse._.Eq₂._≉_
d__'8777'__2004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2004 = erased
-- Function.Bundles._.LeftInverse._.Eq₂.Carrier
d_Carrier_2006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> ()
d_Carrier_2006 = erased
-- Function.Bundles._.LeftInverse._.Eq₂.isEquivalence
d_isEquivalence_2008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2008 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2008 v4 v5 v6
du_isEquivalence_2008 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2008 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.LeftInverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_2010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2010 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2010 v4 v5 v6
du_isPartialEquivalence_2010 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2010 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₂.partialSetoid
d_partialSetoid_2012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2012 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2012 v4 v5 v6
du_partialSetoid_2012 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2012 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4))))
-- Function.Bundles._.LeftInverse._.Eq₂.rawSetoid
d_rawSetoid_2014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_2014 = erased
-- Function.Bundles._.LeftInverse._.Eq₂.refl
d_refl_2016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_refl_2016 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2016 v4 v5 v6
du_refl_2016 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
du_refl_2016 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.LeftInverse._.Eq₂.reflexive
d_reflexive_2018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2018 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2018 v4 v5 v6
du_reflexive_2018 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2018 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.LeftInverse._.Eq₂.setoid
d_setoid_2020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2020 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2020 v4 v5 v6
du_setoid_2020 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2020 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_68
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3)))
-- Function.Bundles._.LeftInverse._.Eq₂.sym
d_sym_2022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2022 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2022 v4 v5 v6
du_sym_2022 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2022 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.LeftInverse._.Eq₂.trans
d_trans_2024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2024 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2024 v4 v5 v6
du_trans_2024 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2024 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.LeftInverse.equivalence
d_equivalence_2026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> T_Equivalence_1858
d_equivalence_2026 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equivalence_2026 v6
du_equivalence_2026 :: T_LeftInverse_1942 -> T_Equivalence_1858
du_equivalence_2026 v0
  = coe
      C_constructor_1940 (coe d_to_1954 (coe v0))
      (coe d_from_1956 (coe v0)) (coe d_to'45'cong_1958 (coe v0))
      (coe d_from'45'cong_1960 (coe v0))
-- Function.Bundles._.LeftInverse.isSplitSurjection
d_isSplitSurjection_2028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_806
d_isSplitSurjection_2028 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSplitSurjection_2028 v4 v5 v6
du_isSplitSurjection_2028 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_806
du_isSplitSurjection_2028 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_888
      (coe d_from_1956 (coe v2))
      (coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.LeftInverse.surjection
d_surjection_2030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> T_Surjection_918
d_surjection_2030 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_surjection_2030 v6
du_surjection_2030 :: T_LeftInverse_1942 -> T_Surjection_918
du_surjection_2030 v0
  = coe
      C_constructor_1002 (coe d_to_1954 (coe v0))
      (coe d_to'45'cong_1958 (coe v0))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_from_1956 v0 v1)
              (coe d_inverse'737'_1962 v0 v1)))
-- Function.Bundles._.RightInverse
d_RightInverse_2036 a0 a1 a2 a3 a4 a5 = ()
data T_RightInverse_2036
  = C_constructor_2120 (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.RightInverse.to
d_to_2048 :: T_RightInverse_2036 -> AgdaAny -> AgdaAny
d_to_2048 v0
  = case coe v0 of
      C_constructor_2120 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.from
d_from_2050 :: T_RightInverse_2036 -> AgdaAny -> AgdaAny
d_from_2050 v0
  = case coe v0 of
      C_constructor_2120 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.to-cong
d_to'45'cong_2052 ::
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_2052 v0
  = case coe v0 of
      C_constructor_2120 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.from-cong
d_from'45'cong_2054 ::
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_2054 v0
  = case coe v0 of
      C_constructor_2120 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.inverseʳ
d_inverse'691'_2056 ::
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_2056 v0
  = case coe v0 of
      C_constructor_2120 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.RightInverse.isCongruent
d_isCongruent_2058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_2058 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_2058 v4 v5 v6
du_isCongruent_2058 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_2058 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_94
      (coe d_to'45'cong_2052 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
-- Function.Bundles._.RightInverse.isRightInverse
d_isRightInverse_2060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438
d_isRightInverse_2060 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isRightInverse_2060 v4 v5 v6
du_isRightInverse_2060 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438
du_isRightInverse_2060 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_520
      (coe du_isCongruent_2058 (coe v0) (coe v1) (coe v2))
      (coe d_from'45'cong_2054 (coe v2))
      (coe d_inverse'691'_2056 (coe v2))
-- Function.Bundles._.RightInverse._.strictlyInverseʳ
d_strictlyInverse'691'_2064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny
d_strictlyInverse'691'_2064 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'691'_2064 v4 v5 v6
du_strictlyInverse'691'_2064 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny
du_strictlyInverse'691'_2064 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'691'_516
      (coe d_to_2048 (coe v2))
      (coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.RightInverse._.Eq₁._≈_
d__'8776'__2068 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2068 = erased
-- Function.Bundles._.RightInverse._.Eq₁._≉_
d__'8777'__2070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2070 = erased
-- Function.Bundles._.RightInverse._.Eq₁.Carrier
d_Carrier_2072 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> ()
d_Carrier_2072 = erased
-- Function.Bundles._.RightInverse._.Eq₁.isEquivalence
d_isEquivalence_2074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2074 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2074 v4 v5 v6
du_isEquivalence_2074 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2074 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.RightInverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_2076 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2076 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2076 v4 v5 v6
du_isPartialEquivalence_2076 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2076 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₁.partialSetoid
d_partialSetoid_2078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2078 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2078 v4 v5 v6
du_partialSetoid_2078 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2078 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.RightInverse._.Eq₁.rawSetoid
d_rawSetoid_2080 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_2080 = erased
-- Function.Bundles._.RightInverse._.Eq₁.refl
d_refl_2082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny
d_refl_2082 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2082 v4 v5 v6
du_refl_2082 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny
du_refl_2082 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.RightInverse._.Eq₁.reflexive
d_reflexive_2084 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2084 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2084 v4 v5 v6
du_reflexive_2084 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2084 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.RightInverse._.Eq₁.setoid
d_setoid_2086 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2086 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2086 v4 v5 v6
du_setoid_2086 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2086 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3)))
-- Function.Bundles._.RightInverse._.Eq₁.sym
d_sym_2088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2088 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2088 v4 v5 v6
du_sym_2088 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2088 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₁.trans
d_trans_2090 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2090 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2090 v4 v5 v6
du_trans_2090 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2090 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₂._≈_
d__'8776'__2094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2094 = erased
-- Function.Bundles._.RightInverse._.Eq₂._≉_
d__'8777'__2096 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2096 = erased
-- Function.Bundles._.RightInverse._.Eq₂.Carrier
d_Carrier_2098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> ()
d_Carrier_2098 = erased
-- Function.Bundles._.RightInverse._.Eq₂.isEquivalence
d_isEquivalence_2100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2100 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2100 v4 v5 v6
du_isEquivalence_2100 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2100 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.RightInverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_2102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2102 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2102 v4 v5 v6
du_isPartialEquivalence_2102 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2102 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₂.partialSetoid
d_partialSetoid_2104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2104 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2104 v4 v5 v6
du_partialSetoid_2104 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2104 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4))))
-- Function.Bundles._.RightInverse._.Eq₂.rawSetoid
d_rawSetoid_2106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_2106 = erased
-- Function.Bundles._.RightInverse._.Eq₂.refl
d_refl_2108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny
d_refl_2108 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2108 v4 v5 v6
du_refl_2108 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny
du_refl_2108 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.RightInverse._.Eq₂.reflexive
d_reflexive_2110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2110 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2110 v4 v5 v6
du_reflexive_2110 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2110 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.RightInverse._.Eq₂.setoid
d_setoid_2112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2112 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2112 v4 v5 v6
du_setoid_2112 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2112 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_68
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3)))
-- Function.Bundles._.RightInverse._.Eq₂.sym
d_sym_2114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2114 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2114 v4 v5 v6
du_sym_2114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2114 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.RightInverse._.Eq₂.trans
d_trans_2116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2116 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2116 v4 v5 v6
du_trans_2116 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2116 v0 v1 v2
  = let v3 = coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.RightInverse.equivalence
d_equivalence_2118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_RightInverse_2036 -> T_Equivalence_1858
d_equivalence_2118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equivalence_2118 v6
du_equivalence_2118 :: T_RightInverse_2036 -> T_Equivalence_1858
du_equivalence_2118 v0
  = coe
      C_constructor_1940 (coe d_to_2048 (coe v0))
      (coe d_from_2050 (coe v0)) (coe d_to'45'cong_2052 (coe v0))
      (coe d_from'45'cong_2054 (coe v0))
-- Function.Bundles._.Inverse
d_Inverse_2122 a0 a1 a2 a3 a4 a5 = ()
data T_Inverse_2122
  = C_constructor_2220 (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Function.Bundles._.Inverse.to
d_to_2134 :: T_Inverse_2122 -> AgdaAny -> AgdaAny
d_to_2134 v0
  = case coe v0 of
      C_constructor_2220 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.from
d_from_2136 :: T_Inverse_2122 -> AgdaAny -> AgdaAny
d_from_2136 v0
  = case coe v0 of
      C_constructor_2220 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.to-cong
d_to'45'cong_2138 ::
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_2138 v0
  = case coe v0 of
      C_constructor_2220 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.from-cong
d_from'45'cong_2140 ::
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_2140 v0
  = case coe v0 of
      C_constructor_2220 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.inverse
d_inverse_2142 ::
  T_Inverse_2122 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2142 v0
  = case coe v0 of
      C_constructor_2220 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.Inverse.inverseˡ
d_inverse'737'_2144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_2144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_inverse'737'_2144 v6 v7 v8
du_inverse'737'_2144 ::
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'737'_2144 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (d_inverse_2142 (coe v0))
      v1 v2
-- Function.Bundles._.Inverse.inverseʳ
d_inverse'691'_2146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_2146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_inverse'691'_2146 v6 v7 v8
du_inverse'691'_2146 ::
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691'_2146 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (d_inverse_2142 (coe v0))
      v1 v2
-- Function.Bundles._.Inverse.leftInverse
d_leftInverse_2148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> T_LeftInverse_1942
d_leftInverse_2148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_leftInverse_2148 v6
du_leftInverse_2148 :: T_Inverse_2122 -> T_LeftInverse_1942
du_leftInverse_2148 v0
  = coe
      C_constructor_2034 (coe d_to_2134 (coe v0))
      (coe d_from_2136 (coe v0)) (coe d_to'45'cong_2138 (coe v0))
      (coe d_from'45'cong_2140 (coe v0))
      (coe du_inverse'737'_2144 (coe v0))
-- Function.Bundles._.Inverse.rightInverse
d_rightInverse_2150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> T_RightInverse_2036
d_rightInverse_2150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_rightInverse_2150 v6
du_rightInverse_2150 :: T_Inverse_2122 -> T_RightInverse_2036
du_rightInverse_2150 v0
  = coe
      C_constructor_2120 (coe d_to_2134 (coe v0))
      (coe d_from_2136 (coe v0)) (coe d_to'45'cong_2138 (coe v0))
      (coe d_from'45'cong_2140 (coe v0))
      (coe du_inverse'691'_2146 (coe v0))
-- Function.Bundles._.Inverse._.isLeftInverse
d_isLeftInverse_2154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
d_isLeftInverse_2154 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isLeftInverse_2154 v4 v5 v6
du_isLeftInverse_2154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
du_isLeftInverse_2154 v0 v1 v2
  = coe
      du_isLeftInverse_1966 (coe v0) (coe v1)
      (coe du_leftInverse_2148 (coe v2))
-- Function.Bundles._.Inverse._.strictlyInverseˡ
d_strictlyInverse'737'_2156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_2156 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'737'_2156 v4 v5 v6
du_strictlyInverse'737'_2156 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_2156 v0 v1 v2
  = let v3 = coe du_leftInverse_2148 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_strictlyInverse'737'_424
         (coe d_from_1956 (coe v3))
         (coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Inverse._.isRightInverse
d_isRightInverse_2160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438
d_isRightInverse_2160 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isRightInverse_2160 v4 v5 v6
du_isRightInverse_2160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438
du_isRightInverse_2160 v0 v1 v2
  = coe
      du_isRightInverse_2060 (coe v0) (coe v1)
      (coe du_rightInverse_2150 (coe v2))
-- Function.Bundles._.Inverse._.strictlyInverseʳ
d_strictlyInverse'691'_2162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny
d_strictlyInverse'691'_2162 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'691'_2162 v4 v5 v6
du_strictlyInverse'691'_2162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny
du_strictlyInverse'691'_2162 v0 v1 v2
  = let v3 = coe du_rightInverse_2150 (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_strictlyInverse'691'_516
         (coe d_to_2048 (coe v3))
         (coe du_isRightInverse_2060 (coe v0) (coe v1) (coe v3)))
-- Function.Bundles._.Inverse.isInverse
d_isInverse_2164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> MAlonzo.Code.Function.Structures.T_IsInverse_526
d_isInverse_2164 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isInverse_2164 v4 v5 v6
du_isInverse_2164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> MAlonzo.Code.Function.Structures.T_IsInverse_526
du_isInverse_2164 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_618
      (coe
         du_isLeftInverse_1966 (coe v0) (coe v1)
         (coe du_leftInverse_2148 (coe v2)))
      (coe du_inverse'691'_2146 (coe v2))
-- Function.Bundles._.Inverse._.Eq₁._≈_
d__'8776'__2170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2170 = erased
-- Function.Bundles._.Inverse._.Eq₁._≉_
d__'8777'__2172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2172 = erased
-- Function.Bundles._.Inverse._.Eq₁.Carrier
d_Carrier_2174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> ()
d_Carrier_2174 = erased
-- Function.Bundles._.Inverse._.Eq₁.isEquivalence
d_isEquivalence_2176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2176 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2176 v4 v5 v6
du_isEquivalence_2176 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2176 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v5))))
-- Function.Bundles._.Inverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_2178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2178 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2178 v4 v5 v6
du_isPartialEquivalence_2178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2178 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₁.partialSetoid
d_partialSetoid_2180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2180 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2180 v4 v5 v6
du_partialSetoid_2180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2180 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
               (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5)))))
-- Function.Bundles._.Inverse._.Eq₁.rawSetoid
d_rawSetoid_2182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_2182 = erased
-- Function.Bundles._.Inverse._.Eq₁.refl
d_refl_2184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny
d_refl_2184 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2184 v4 v5 v6
du_refl_2184 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny
du_refl_2184 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
                  (coe v5)))))
-- Function.Bundles._.Inverse._.Eq₁.reflexive
d_reflexive_2186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2186 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2186 v4 v5 v6
du_reflexive_2186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2186 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (\ v7 v8 v9 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v6))
                    v7))))
-- Function.Bundles._.Inverse._.Eq₁.setoid
d_setoid_2188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2188 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2188 v4 v5 v6
du_setoid_2188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2188 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_40
            (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4))))
-- Function.Bundles._.Inverse._.Eq₁.sym
d_sym_2190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2190 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2190 v4 v5 v6
du_sym_2190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2190 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₁.trans
d_trans_2192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2192 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2192 v4 v5 v6
du_trans_2192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2192 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₂._≈_
d__'8776'__2196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2196 = erased
-- Function.Bundles._.Inverse._.Eq₂._≉_
d__'8777'__2198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2198 = erased
-- Function.Bundles._.Inverse._.Eq₂.Carrier
d_Carrier_2200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> ()
d_Carrier_2200 = erased
-- Function.Bundles._.Inverse._.Eq₂.isEquivalence
d_isEquivalence_2202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2202 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2202 v4 v5 v6
du_isEquivalence_2202 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2202 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v5))))
-- Function.Bundles._.Inverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_2204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2204 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2204 v4 v5 v6
du_isPartialEquivalence_2204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2204 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₂.partialSetoid
d_partialSetoid_2206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2206 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2206 v4 v5 v6
du_partialSetoid_2206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2206 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
               (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5)))))
-- Function.Bundles._.Inverse._.Eq₂.rawSetoid
d_rawSetoid_2208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_2208 = erased
-- Function.Bundles._.Inverse._.Eq₂.refl
d_refl_2210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny
d_refl_2210 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2210 v4 v5 v6
du_refl_2210 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny
du_refl_2210 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
                  (coe v5)))))
-- Function.Bundles._.Inverse._.Eq₂.reflexive
d_reflexive_2212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2212 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2212 v4 v5 v6
du_reflexive_2212 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2212 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5) in
             coe
               (\ v7 v8 v9 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v6))
                    v7))))
-- Function.Bundles._.Inverse._.Eq₂.setoid
d_setoid_2214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2214 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2214 v4 v5 v6
du_setoid_2214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2214 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_68
            (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4))))
-- Function.Bundles._.Inverse._.Eq₂.sym
d_sym_2216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2216 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2216 v4 v5 v6
du_sym_2216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2216 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.Inverse._.Eq₂.trans
d_trans_2218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2218 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2218 v4 v5 v6
du_trans_2218 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_Inverse_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2218 v0 v1 v2
  = let v3 = coe du_isInverse_2164 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3) in
       coe
         (let v5
                = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v4) in
          coe
            (let v6
                   = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v5) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                     (coe v6))))))
-- Function.Bundles._.BiEquivalence
d_BiEquivalence_2222 a0 a1 a2 a3 a4 a5 = ()
data T_BiEquivalence_2222
  = C_constructor_2248 (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.BiEquivalence.to
d_to_2236 :: T_BiEquivalence_2222 -> AgdaAny -> AgdaAny
d_to_2236 v0
  = case coe v0 of
      C_constructor_2248 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.from₁
d_from'8321'_2238 :: T_BiEquivalence_2222 -> AgdaAny -> AgdaAny
d_from'8321'_2238 v0
  = case coe v0 of
      C_constructor_2248 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.from₂
d_from'8322'_2240 :: T_BiEquivalence_2222 -> AgdaAny -> AgdaAny
d_from'8322'_2240 v0
  = case coe v0 of
      C_constructor_2248 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.to-cong
d_to'45'cong_2242 ::
  T_BiEquivalence_2222 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_2242 v0
  = case coe v0 of
      C_constructor_2248 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.from₁-cong
d_from'8321''45'cong_2244 ::
  T_BiEquivalence_2222 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8321''45'cong_2244 v0
  = case coe v0 of
      C_constructor_2248 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiEquivalence.from₂-cong
d_from'8322''45'cong_2246 ::
  T_BiEquivalence_2222 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8322''45'cong_2246 v0
  = case coe v0 of
      C_constructor_2248 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse
d_BiInverse_2250 a0 a1 a2 a3 a4 a5 = ()
data T_BiInverse_2250
  = C_constructor_2290 (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Bundles._.BiInverse.to
d_to_2268 :: T_BiInverse_2250 -> AgdaAny -> AgdaAny
d_to_2268 v0
  = case coe v0 of
      C_constructor_2290 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.from₁
d_from'8321'_2270 :: T_BiInverse_2250 -> AgdaAny -> AgdaAny
d_from'8321'_2270 v0
  = case coe v0 of
      C_constructor_2290 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.from₂
d_from'8322'_2272 :: T_BiInverse_2250 -> AgdaAny -> AgdaAny
d_from'8322'_2272 v0
  = case coe v0 of
      C_constructor_2290 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.to-cong
d_to'45'cong_2274 ::
  T_BiInverse_2250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_2274 v0
  = case coe v0 of
      C_constructor_2290 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.from₁-cong
d_from'8321''45'cong_2276 ::
  T_BiInverse_2250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8321''45'cong_2276 v0
  = case coe v0 of
      C_constructor_2290 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.from₂-cong
d_from'8322''45'cong_2278 ::
  T_BiInverse_2250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8322''45'cong_2278 v0
  = case coe v0 of
      C_constructor_2290 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.inverseˡ
d_inverse'737'_2280 ::
  T_BiInverse_2250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_2280 v0
  = case coe v0 of
      C_constructor_2290 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.inverseʳ
d_inverse'691'_2282 ::
  T_BiInverse_2250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_2282 v0
  = case coe v0 of
      C_constructor_2290 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Bundles._.BiInverse.to-isCongruent
d_to'45'isCongruent_2284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_BiInverse_2250 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_to'45'isCongruent_2284 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_to'45'isCongruent_2284 v4 v5 v6
du_to'45'isCongruent_2284 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_BiInverse_2250 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_to'45'isCongruent_2284 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_94
      (coe d_to'45'cong_2274 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
-- Function.Bundles._.BiInverse.isBiInverse
d_isBiInverse_2286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_BiInverse_2250 ->
  MAlonzo.Code.Function.Structures.T_IsBiInverse_714
d_isBiInverse_2286 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isBiInverse_2286 v4 v5 v6
du_isBiInverse_2286 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_BiInverse_2250 ->
  MAlonzo.Code.Function.Structures.T_IsBiInverse_714
du_isBiInverse_2286 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_802
      (coe du_to'45'isCongruent_2284 (coe v0) (coe v1) (coe v2))
      (coe d_from'8321''45'cong_2276 (coe v2))
      (coe d_from'8322''45'cong_2278 (coe v2))
      (coe d_inverse'737'_2280 (coe v2))
      (coe d_inverse'691'_2282 (coe v2))
-- Function.Bundles._.BiInverse.biEquivalence
d_biEquivalence_2288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_BiInverse_2250 -> T_BiEquivalence_2222
d_biEquivalence_2288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_biEquivalence_2288 v6
du_biEquivalence_2288 :: T_BiInverse_2250 -> T_BiEquivalence_2222
du_biEquivalence_2288 v0
  = coe
      C_constructor_2248 (coe d_to_2268 (coe v0))
      (coe d_from'8321'_2270 (coe v0)) (coe d_from'8322'_2272 (coe v0))
      (coe d_to'45'cong_2274 (coe v0))
      (coe d_from'8321''45'cong_2276 (coe v0))
      (coe d_from'8322''45'cong_2278 (coe v0))
-- Function.Bundles._.SplitSurjection
d_SplitSurjection_2292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 -> ()
d_SplitSurjection_2292 = erased
-- Function.Bundles._.SplitSurjection.equivalence
d_equivalence_2298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> T_Equivalence_1858
d_equivalence_2298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equivalence_2298 v6
du_equivalence_2298 :: T_LeftInverse_1942 -> T_Equivalence_1858
du_equivalence_2298 v0 = coe du_equivalence_2026 (coe v0)
-- Function.Bundles._.SplitSurjection.from
d_from_2300 :: T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_from_2300 v0 = coe d_from_1956 (coe v0)
-- Function.Bundles._.SplitSurjection.from-cong
d_from'45'cong_2302 ::
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_2302 v0 = coe d_from'45'cong_1960 (coe v0)
-- Function.Bundles._.SplitSurjection.inverseˡ
d_inverse'737'_2304 ::
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_2304 v0 = coe d_inverse'737'_1962 (coe v0)
-- Function.Bundles._.SplitSurjection.isCongruent
d_isCongruent_2306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_2306 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isCongruent_2306 v4 v5 v6
du_isCongruent_2306 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_2306 v0 v1 v2
  = coe du_isCongruent_1964 (coe v0) (coe v1) (coe v2)
-- Function.Bundles._.SplitSurjection.isLeftInverse
d_isLeftInverse_2308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
d_isLeftInverse_2308 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isLeftInverse_2308 v4 v5 v6
du_isLeftInverse_2308 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
du_isLeftInverse_2308 v0 v1 v2
  = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2)
-- Function.Bundles._.SplitSurjection.isSplitSurjection
d_isSplitSurjection_2310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_806
d_isSplitSurjection_2310 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSplitSurjection_2310 v4 v5 v6
du_isSplitSurjection_2310 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsSplitSurjection_806
du_isSplitSurjection_2310 v0 v1 v2
  = coe du_isSplitSurjection_2028 (coe v0) (coe v1) (coe v2)
-- Function.Bundles._.SplitSurjection.isSurjection
d_isSurjection_2312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
d_isSurjection_2312 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isSurjection_2312 v4 v5 v6
du_isSurjection_2312 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
du_isSurjection_2312 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_isSurjection_428
      (coe d_from_1956 (coe v2))
      (coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.SplitSurjection.strictlyInverseˡ
d_strictlyInverse'737'_2314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_2314 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_strictlyInverse'737'_2314 v4 v5 v6
du_strictlyInverse'737'_2314 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_2314 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.du_strictlyInverse'737'_424
      (coe d_from_1956 (coe v2))
      (coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2))
-- Function.Bundles._.SplitSurjection.surjection
d_surjection_2316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> T_Surjection_918
d_surjection_2316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_surjection_2316 v6
du_surjection_2316 :: T_LeftInverse_1942 -> T_Surjection_918
du_surjection_2316 v0 = coe du_surjection_2030 (coe v0)
-- Function.Bundles._.SplitSurjection.to
d_to_2318 :: T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_to_2318 v0 = coe d_to_1954 (coe v0)
-- Function.Bundles._.SplitSurjection.to-cong
d_to'45'cong_2320 ::
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'cong_2320 v0 = coe d_to'45'cong_1958 (coe v0)
-- Function.Bundles._.SplitSurjection.Eq₁._≈_
d__'8776'__2324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2324 = erased
-- Function.Bundles._.SplitSurjection.Eq₁._≉_
d__'8777'__2326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2326 = erased
-- Function.Bundles._.SplitSurjection.Eq₁.Carrier
d_Carrier_2328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> ()
d_Carrier_2328 = erased
-- Function.Bundles._.SplitSurjection.Eq₁.isEquivalence
d_isEquivalence_2330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2330 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2330 v4 v5 v6
du_isEquivalence_2330 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2330 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v4)))
-- Function.Bundles._.SplitSurjection.Eq₁.isPartialEquivalence
d_isPartialEquivalence_2332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2332 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2332 v4 v5 v6
du_isPartialEquivalence_2332 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2332 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₁.partialSetoid
d_partialSetoid_2334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2334 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2334 v4 v5 v6
du_partialSetoid_2334 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2334 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4))))
-- Function.Bundles._.SplitSurjection.Eq₁.rawSetoid
d_rawSetoid_2336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_2336 = erased
-- Function.Bundles._.SplitSurjection.Eq₁.refl
d_refl_2338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_refl_2338 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2338 v4 v5 v6
du_refl_2338 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
du_refl_2338 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
               (coe v4))))
-- Function.Bundles._.SplitSurjection.Eq₁.reflexive
d_reflexive_2340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2340 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2340 v4 v5 v6
du_reflexive_2340 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2340 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.SplitSurjection.Eq₁.setoid
d_setoid_2342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2342 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2342 v4 v5 v6
du_setoid_2342 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2342 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_40
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3)))
-- Function.Bundles._.SplitSurjection.Eq₁.sym
d_sym_2344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2344 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2344 v4 v5 v6
du_sym_2344 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2344 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₁.trans
d_trans_2346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2346 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2346 v4 v5 v6
du_trans_2346 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2346 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₂._≈_
d__'8776'__2350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> ()
d__'8776'__2350 = erased
-- Function.Bundles._.SplitSurjection.Eq₂._≉_
d__'8777'__2352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> ()
d__'8777'__2352 = erased
-- Function.Bundles._.SplitSurjection.Eq₂.Carrier
d_Carrier_2354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> ()
d_Carrier_2354 = erased
-- Function.Bundles._.SplitSurjection.Eq₂.isEquivalence
d_isEquivalence_2356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_2356 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isEquivalence_2356 v4 v5 v6
du_isEquivalence_2356 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_2356 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v4)))
-- Function.Bundles._.SplitSurjection.Eq₂.isPartialEquivalence
d_isPartialEquivalence_2358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_2358 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_isPartialEquivalence_2358 v4 v5 v6
du_isPartialEquivalence_2358 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_2358 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₂.partialSetoid
d_partialSetoid_2360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_2360 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_partialSetoid_2360 v4 v5 v6
du_partialSetoid_2360 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_2360 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_72
            (coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4))))
-- Function.Bundles._.SplitSurjection.Eq₂.rawSetoid
d_rawSetoid_2362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_2362 = erased
-- Function.Bundles._.SplitSurjection.Eq₂.refl
d_refl_2364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
d_refl_2364 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_refl_2364 v4 v5 v6
du_refl_2364 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny
du_refl_2364 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
               (coe v4))))
-- Function.Bundles._.SplitSurjection.Eq₂.reflexive
d_reflexive_2366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_2366 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_reflexive_2366 v4 v5 v6
du_reflexive_2366 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_2366 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (\ v6 v7 v8 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v5))
                 v6)))
-- Function.Bundles._.SplitSurjection.Eq₂.setoid
d_setoid_2368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_2368 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_setoid_2368 v4 v5 v6
du_setoid_2368 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_2368 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.du_setoid_68
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3)))
-- Function.Bundles._.SplitSurjection.Eq₂.sym
d_sym_2370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_2370 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_2370 v4 v5 v6
du_sym_2370 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_2370 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._.SplitSurjection.Eq₂.trans
d_trans_2372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_2372 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_trans_2372 v4 v5 v6
du_trans_2372 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  T_LeftInverse_1942 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_2372 v0 v1 v2
  = let v3 = coe du_isLeftInverse_1966 (coe v0) (coe v1) (coe v2) in
    coe
      (let v4
             = MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3) in
       coe
         (let v5
                = coe MAlonzo.Code.Function.Structures.du_setoid_68 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                  (coe v5)))))
-- Function.Bundles._⟶ₛ_
d__'10230''8347'__2374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 -> ()
d__'10230''8347'__2374 = erased
-- Function.Bundles._⟶_
d__'10230'__2376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'10230'__2376 = erased
-- Function.Bundles._↣_
d__'8611'__2382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8611'__2382 = erased
-- Function.Bundles._↠_
d__'8608'__2388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8608'__2388 = erased
-- Function.Bundles._⤖_
d__'10518'__2394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'10518'__2394 = erased
-- Function.Bundles._⇔_
d__'8660'__2400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8660'__2400 = erased
-- Function.Bundles._↩_
d__'8617'__2406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8617'__2406 = erased
-- Function.Bundles._↪_
d__'8618'__2412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8618'__2412 = erased
-- Function.Bundles._↩↪_
d__'8617''8618'__2418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8617''8618'__2418 = erased
-- Function.Bundles._↔_
d__'8596'__2424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> () -> ()
d__'8596'__2424 = erased
-- Function.Bundles._.mk⟶
d_mk'10230'_2442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> T_Func_774
d_mk'10230'_2442 ~v0 ~v1 ~v2 ~v3 v4 = du_mk'10230'_2442 v4
du_mk'10230'_2442 :: (AgdaAny -> AgdaAny) -> T_Func_774
du_mk'10230'_2442 v0 = coe C_constructor_840 (coe v0) erased
-- Function.Bundles._.mk↣
d_mk'8611'_2448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_Injection_842
d_mk'8611'_2448 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mk'8611'_2448 v4 v5
du_mk'8611'_2448 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_Injection_842
du_mk'8611'_2448 v0 v1
  = coe C_constructor_916 (coe v0) erased (coe v1)
-- Function.Bundles._.mk↠
d_mk'8608'_2456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Surjection_918
d_mk'8608'_2456 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mk'8608'_2456 v4 v5
du_mk'8608'_2456 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Surjection_918
du_mk'8608'_2456 v0 v1
  = coe C_constructor_1002 (coe v0) erased (coe v1)
-- Function.Bundles._.mk⤖
d_mk'10518'_2464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Bijection_1004
d_mk'10518'_2464 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mk'10518'_2464 v4 v5
du_mk'10518'_2464 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Bijection_1004
du_mk'10518'_2464 v0 v1
  = coe C_constructor_1094 (coe v0) erased (coe v1)
-- Function.Bundles._.mk⇔
d_mk'8660'_2474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Equivalence_1858
d_mk'8660'_2474 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mk'8660'_2474 v4 v5
du_mk'8660'_2474 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Equivalence_1858
du_mk'8660'_2474 v0 v1
  = coe C_constructor_1940 (coe v0) (coe v1) erased erased
-- Function.Bundles._.mk↩
d_mk'8617'_2484 ::
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
  T_LeftInverse_1942
d_mk'8617'_2484 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_mk'8617'_2484 v4 v5 v6
du_mk'8617'_2484 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_LeftInverse_1942
du_mk'8617'_2484 v0 v1 v2
  = coe C_constructor_2034 (coe v0) (coe v1) erased erased (coe v2)
-- Function.Bundles._.mk↪
d_mk'8618'_2496 ::
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
  T_RightInverse_2036
d_mk'8618'_2496 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_mk'8618'_2496 v4 v5 v6
du_mk'8618'_2496 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_RightInverse_2036
du_mk'8618'_2496 v0 v1 v2
  = coe C_constructor_2120 (coe v0) (coe v1) erased erased (coe v2)
-- Function.Bundles._.mk↩↪
d_mk'8617''8618'_2510 ::
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
  T_BiInverse_2250
d_mk'8617''8618'_2510 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_mk'8617''8618'_2510 v4 v5 v6 v7 v8
du_mk'8617''8618'_2510 ::
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
  T_BiInverse_2250
du_mk'8617''8618'_2510 v0 v1 v2 v3 v4
  = coe
      C_constructor_2290 (coe v0) (coe v1) (coe v2) erased erased erased
      (coe v3) (coe v4)
-- Function.Bundles._.mk↔
d_mk'8596'_2526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Inverse_2122
d_mk'8596'_2526 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_mk'8596'_2526 v4 v5 v6
du_mk'8596'_2526 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Inverse_2122
du_mk'8596'_2526 v0 v1 v2
  = coe C_constructor_2220 (coe v0) (coe v1) erased erased (coe v2)
-- Function.Bundles._.mk↠ₛ
d_mk'8608''8347'_2536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Surjection_918
d_mk'8608''8347'_2536 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_mk'8608''8347'_2536 v4 v5
du_mk'8608''8347'_2536 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Surjection_918
du_mk'8608''8347'_2536 v0 v1
  = coe
      du_mk'8608'_2456 (coe v0)
      (coe
         MAlonzo.Code.Function.Consequences.Propositional.du_strictlySurjective'8658'surjective_40
         v0 v1)
-- Function.Bundles._.mk↔ₛ′
d_mk'8596''8347''8242'_2542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_Inverse_2122
d_mk'8596''8347''8242'_2542 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_mk'8596''8347''8242'_2542 v4 v5
du_mk'8596''8347''8242'_2542 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_Inverse_2122
du_mk'8596''8347''8242'_2542 v0 v1
  = coe
      du_mk'8596'_2526 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Function.Bundles._._⟨$⟩_
d__'10216''36''10217'__2568 :: T_Func_774 -> AgdaAny -> AgdaAny
d__'10216''36''10217'__2568 v0 = coe d_to_780 (coe v0)
