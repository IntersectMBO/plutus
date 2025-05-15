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

module MAlonzo.Code.Function.Structures.Biased where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Consequences.Setoid qualified
import MAlonzo.Code.Function.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Structures.Biased._.IsBijection
d_IsBijection_28 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Function.Structures.Biased._.IsCongruent
d_IsCongruent_30 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Function.Structures.Biased._.IsInjection
d_IsInjection_32 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Function.Structures.Biased._.IsInverse
d_IsInverse_34 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Function.Structures.Biased._.IsLeftInverse
d_IsLeftInverse_36 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Function.Structures.Biased._.IsRightInverse
d_IsRightInverse_38 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Function.Structures.Biased._.IsSurjection
d_IsSurjection_42 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Function.Structures.Biased._.IsBijection.isInjection
d_isInjection_186 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
d_isInjection_186 v0
  = coe MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v0)
-- Function.Structures.Biased._.IsBijection.surjective
d_surjective_192 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_192 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_248 (coe v0)
-- Function.Structures.Biased._.IsCongruent.cong
d_cong_244 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_244 v0
  = coe MAlonzo.Code.Function.Structures.d_cong_32 (coe v0)
-- Function.Structures.Biased._.IsCongruent.isEquivalence₁
d_isEquivalence'8321'_246 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_246 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Structures.Biased._.IsCongruent.isEquivalence₂
d_isEquivalence'8322'_248 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_248 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Structures.Biased._.IsCongruent.Eq₁._≈_
d__'8776'__252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__252 = erased
-- Function.Structures.Biased._.IsCongruent.Eq₁._≉_
d__'8777'__254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__254 = erased
-- Function.Structures.Biased._.IsCongruent.Eq₁.Carrier
d_Carrier_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 -> ()
d_Carrier_256 = erased
-- Function.Structures.Biased._.IsCongruent.Eq₁.isEquivalence
d_isEquivalence_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_258 v9
du_isEquivalence_258 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_258 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0)
-- Function.Structures.Biased._.IsCongruent.Eq₁.isPartialEquivalence
d_isPartialEquivalence_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_260 v9
du_isPartialEquivalence_260 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_260 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.Biased._.IsCongruent.Eq₁.partialSetoid
d_partialSetoid_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_262 v9
du_partialSetoid_262 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_262 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
      (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0))
-- Function.Structures.Biased._.IsCongruent.Eq₁.refl
d_refl_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
d_refl_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_264 v9
du_refl_264 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
du_refl_264 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0))
-- Function.Structures.Biased._.IsCongruent.Eq₁.reflexive
d_reflexive_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_266 v9
du_reflexive_266 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_266 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
           v2)
-- Function.Structures.Biased._.IsCongruent.Eq₁.setoid
d_setoid_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_setoid_268
du_setoid_268 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_268 v0 v1
  = coe MAlonzo.Code.Function.Structures.du_setoid_40 v1
-- Function.Structures.Biased._.IsCongruent.Eq₁.sym
d_sym_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_270 v9
du_sym_270 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_270 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.Biased._.IsCongruent.Eq₁.trans
d_trans_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_272 v9
du_trans_272 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_272 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.Biased._.IsCongruent.Eq₂._≈_
d__'8776'__276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__276 = erased
-- Function.Structures.Biased._.IsCongruent.Eq₂._≉_
d__'8777'__278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__278 = erased
-- Function.Structures.Biased._.IsCongruent.Eq₂.Carrier
d_Carrier_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 -> ()
d_Carrier_280 = erased
-- Function.Structures.Biased._.IsCongruent.Eq₂.isEquivalence
d_isEquivalence_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_282 v9
du_isEquivalence_282 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_282 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0)
-- Function.Structures.Biased._.IsCongruent.Eq₂.isPartialEquivalence
d_isPartialEquivalence_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_284 v9
du_isPartialEquivalence_284 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_284 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.Biased._.IsCongruent.Eq₂.partialSetoid
d_partialSetoid_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_286 v9
du_partialSetoid_286 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_286 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
      (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0))
-- Function.Structures.Biased._.IsCongruent.Eq₂.refl
d_refl_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
d_refl_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_288 v9
du_refl_288 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny
du_refl_288 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0))
-- Function.Structures.Biased._.IsCongruent.Eq₂.reflexive
d_reflexive_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_290 v9
du_reflexive_290 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_290 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
           v2)
-- Function.Structures.Biased._.IsCongruent.Eq₂.setoid
d_setoid_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_setoid_292
du_setoid_292 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_292 v0 v1
  = coe MAlonzo.Code.Function.Structures.du_setoid_66 v1
-- Function.Structures.Biased._.IsCongruent.Eq₂.sym
d_sym_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_294 v9
du_sym_294 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_294 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.Biased._.IsCongruent.Eq₂.trans
d_trans_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_296 v9
du_trans_296 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_296 v0
  = let v1
          = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.Biased._.IsInjection.injective
d_injective_302 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_302 v0
  = coe MAlonzo.Code.Function.Structures.d_injective_102 (coe v0)
-- Function.Structures.Biased._.IsInjection.isCongruent
d_isCongruent_304 ::
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_304 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v0)
-- Function.Structures.Biased._.IsInverse.inverseʳ
d_inverse'691'_364 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_364 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_502 (coe v0)
-- Function.Structures.Biased._.IsInverse.isLeftInverse
d_isLeftInverse_374 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_374 v0
  = coe MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0)
-- Function.Structures.Biased._.IsLeftInverse.from-cong
d_from'45'cong_436 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_436 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_336 (coe v0)
-- Function.Structures.Biased._.IsLeftInverse.inverseˡ
d_inverse'737'_438 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_438 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'737'_338 (coe v0)
-- Function.Structures.Biased._.IsLeftInverse.isCongruent
d_isCongruent_440 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_440 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0)
-- Function.Structures.Biased._.IsRightInverse.from-cong
d_from'45'cong_502 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_502 v0
  = coe MAlonzo.Code.Function.Structures.d_from'45'cong_422 (coe v0)
-- Function.Structures.Biased._.IsRightInverse.inverseʳ
d_inverse'691'_504 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_504 v0
  = coe MAlonzo.Code.Function.Structures.d_inverse'691'_424 (coe v0)
-- Function.Structures.Biased._.IsRightInverse.isCongruent
d_isCongruent_506 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_506 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0)
-- Function.Structures.Biased._.IsSurjection.isCongruent
d_isCongruent_638 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_638 v0
  = coe MAlonzo.Code.Function.Structures.d_isCongruent_170 (coe v0)
-- Function.Structures.Biased._.IsSurjection.surjective
d_surjective_646 ::
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_646 v0
  = coe MAlonzo.Code.Function.Structures.d_surjective_172 (coe v0)
-- Function.Structures.Biased.IsStrictSurjection
d_IsStrictSurjection_698 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsStrictSurjection_698
  = C_IsStrictSurjection'46'constructor_13287 MAlonzo.Code.Function.Structures.T_IsCongruent_22
                                              (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Function.Structures.Biased.IsStrictSurjection.isCongruent
d_isCongruent_706 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_706 v0
  = case coe v0 of
      C_IsStrictSurjection'46'constructor_13287 v1 v2 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictSurjection.strictlySurjective
d_strictlySurjective_708 ::
  T_IsStrictSurjection_698 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_708 v0
  = case coe v0 of
      C_IsStrictSurjection'46'constructor_13287 v1 v2 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictSurjection._.cong
d_cong_712 ::
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_712 v0
  = coe
      MAlonzo.Code.Function.Structures.d_cong_32
      (coe d_isCongruent_706 (coe v0))
-- Function.Structures.Biased.IsStrictSurjection._.isEquivalence₁
d_isEquivalence'8321'_714 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_714 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
      (coe d_isCongruent_706 (coe v0))
-- Function.Structures.Biased.IsStrictSurjection._.isEquivalence₂
d_isEquivalence'8322'_716 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_716 v0
  = coe
      MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
      (coe d_isCongruent_706 (coe v0))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁._≈_
d__'8776'__720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 -> AgdaAny -> AgdaAny -> ()
d__'8776'__720 = erased
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁._≉_
d__'8777'__722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 -> AgdaAny -> AgdaAny -> ()
d__'8777'__722 = erased
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.Carrier
d_Carrier_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsStrictSurjection_698 -> ()
d_Carrier_724 = erased
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.isEquivalence
d_isEquivalence_726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_726 v9
du_isEquivalence_726 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_726 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_728 v9
du_isPartialEquivalence_728 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_728 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.partialSetoid
d_partialSetoid_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_730 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_730 v9
du_partialSetoid_730 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_730 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1)))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.refl
d_refl_732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 -> AgdaAny -> AgdaAny
d_refl_732 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_732 v9
du_refl_732 :: T_IsStrictSurjection_698 -> AgdaAny -> AgdaAny
du_refl_732 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v1)))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.reflexive
d_reflexive_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_734 v9
du_reflexive_734 ::
  T_IsStrictSurjection_698 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_734 v0
  = let v1 = d_isCongruent_706 (coe v0) in
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
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.setoid
d_setoid_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_736 v9
du_setoid_736 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_736 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe d_isCongruent_706 (coe v0))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.sym
d_sym_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_738 v9
du_sym_738 ::
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_738 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₁.trans
d_trans_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_740 v9
du_trans_740 ::
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_740 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂._≈_
d__'8776'__744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 -> AgdaAny -> AgdaAny -> ()
d__'8776'__744 = erased
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂._≉_
d__'8777'__746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 -> AgdaAny -> AgdaAny -> ()
d__'8777'__746 = erased
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.Carrier
d_Carrier_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsStrictSurjection_698 -> ()
d_Carrier_748 = erased
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.isEquivalence
d_isEquivalence_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_750 v9
du_isEquivalence_750 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_750 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_752 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_752 v9
du_isPartialEquivalence_752 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_752 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.partialSetoid
d_partialSetoid_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_754 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_754 v9
du_partialSetoid_754 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_754 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1)))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.refl
d_refl_756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 -> AgdaAny -> AgdaAny
d_refl_756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_756 v9
du_refl_756 :: T_IsStrictSurjection_698 -> AgdaAny -> AgdaAny
du_refl_756 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v1)))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.reflexive
d_reflexive_758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_758 v9
du_reflexive_758 ::
  T_IsStrictSurjection_698 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_758 v0
  = let v1 = d_isCongruent_706 (coe v0) in
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
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.setoid
d_setoid_760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_760 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_760 v9
du_setoid_760 ::
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_760 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_66
      (coe d_isCongruent_706 (coe v0))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.sym
d_sym_762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_762 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_762 v9
du_sym_762 ::
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_762 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictSurjection._.Eq₂.trans
d_trans_764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_764 v9
du_trans_764 ::
  T_IsStrictSurjection_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_764 v0
  = let v1 = d_isCongruent_706 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictSurjection.isSurjection
d_isSurjection_766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
d_isSurjection_766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_isSurjection_766 v8 v9
du_isSurjection_766 ::
  (AgdaAny -> AgdaAny) ->
  T_IsStrictSurjection_698 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
du_isSurjection_766 v0 v1
  = coe
      MAlonzo.Code.Function.Structures.C_IsSurjection'46'constructor_6463
      (coe d_isCongruent_706 (coe v1))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_strictlySurjective'8658'surjective_84
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_66
            (coe d_isCongruent_706 (coe v1)))
         v0
         (MAlonzo.Code.Function.Structures.d_cong_32
            (coe d_isCongruent_706 (coe v1)))
         (d_strictlySurjective_708 (coe v1)))
-- Function.Structures.Biased.IsStrictBijection
d_IsStrictBijection_770 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsStrictBijection_770
  = C_IsStrictBijection'46'constructor_16375 MAlonzo.Code.Function.Structures.T_IsInjection_92
                                             (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Function.Structures.Biased.IsStrictBijection.isInjection
d_isInjection_778 ::
  T_IsStrictBijection_770 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
d_isInjection_778 v0
  = case coe v0 of
      C_IsStrictBijection'46'constructor_16375 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictBijection.strictlySurjective
d_strictlySurjective_780 ::
  T_IsStrictBijection_770 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_780 v0
  = case coe v0 of
      C_IsStrictBijection'46'constructor_16375 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictBijection.isBijection
d_isBijection_782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictBijection_770 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
d_isBijection_782 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_isBijection_782 v8 v9
du_isBijection_782 ::
  (AgdaAny -> AgdaAny) ->
  T_IsStrictBijection_770 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
du_isBijection_782 v0 v1
  = coe
      MAlonzo.Code.Function.Structures.C_IsBijection'46'constructor_10113
      (coe d_isInjection_778 (coe v1))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_strictlySurjective'8658'surjective_84
         (let v2 = d_isInjection_778 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.du_setoid_66
               (coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v2))))
         v0
         (MAlonzo.Code.Function.Structures.d_cong_32
            (coe
               MAlonzo.Code.Function.Structures.d_isCongruent_100
               (coe d_isInjection_778 (coe v1))))
         (d_strictlySurjective_780 (coe v1)))
-- Function.Structures.Biased.IsStrictLeftInverse
d_IsStrictLeftInverse_852 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsStrictLeftInverse_852
  = C_IsStrictLeftInverse'46'constructor_20167 MAlonzo.Code.Function.Structures.T_IsCongruent_22
                                               (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                               (AgdaAny -> AgdaAny)
-- Function.Structures.Biased.IsStrictLeftInverse.isCongruent
d_isCongruent_864 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_864 v0
  = case coe v0 of
      C_IsStrictLeftInverse'46'constructor_20167 v1 v2 v3 -> coe v1
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictLeftInverse.from-cong
d_from'45'cong_866 ::
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_866 v0
  = case coe v0 of
      C_IsStrictLeftInverse'46'constructor_20167 v1 v2 v3 -> coe v2
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictLeftInverse.strictlyInverseˡ
d_strictlyInverse'737'_868 ::
  T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_868 v0
  = case coe v0 of
      C_IsStrictLeftInverse'46'constructor_20167 v1 v2 v3 -> coe v3
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictLeftInverse.isLeftInverse
d_isLeftInverse_870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_870 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_isLeftInverse_870 v8 v9 v10
du_isLeftInverse_870 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
du_isLeftInverse_870 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsLeftInverse'46'constructor_14363
      (coe d_isCongruent_864 (coe v2)) (coe d_from'45'cong_866 (coe v2))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_strictlyInverse'737''8658'inverse'737'_88
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_66
            (coe d_isCongruent_864 (coe v2)))
         v0 v1
         (MAlonzo.Code.Function.Structures.d_cong_32
            (coe d_isCongruent_864 (coe v2)))
         (d_strictlyInverse'737'_868 (coe v2)))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁._≈_
d__'8776'__886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny -> ()
d__'8776'__886 = erased
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁._≉_
d__'8777'__888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny -> ()
d__'8777'__888 = erased
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.Carrier
d_Carrier_890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsStrictLeftInverse_852 -> ()
d_Carrier_890 = erased
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.isEquivalence
d_isEquivalence_892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_892 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_892 v10
du_isEquivalence_892 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_892 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_894 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_894 v10
du_isPartialEquivalence_894 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_894 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.partialSetoid
d_partialSetoid_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_896 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_896 v10
du_partialSetoid_896 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_896 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1)))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.refl
d_refl_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny
d_refl_898 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_898 v10
du_refl_898 :: T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny
du_refl_898 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v1)))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.reflexive
d_reflexive_900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_900 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_900 v10
du_reflexive_900 ::
  T_IsStrictLeftInverse_852 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_900 v0
  = let v1 = d_isCongruent_864 (coe v0) in
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
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.setoid
d_setoid_902 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_902 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_902 v10
du_setoid_902 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_902 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe d_isCongruent_864 (coe v0))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.sym
d_sym_904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_904 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_904 v10
du_sym_904 ::
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_904 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₁.trans
d_trans_906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_906 v10
du_trans_906 ::
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_906 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂._≈_
d__'8776'__910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny -> ()
d__'8776'__910 = erased
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂._≉_
d__'8777'__912 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny -> ()
d__'8777'__912 = erased
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.Carrier
d_Carrier_914 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsStrictLeftInverse_852 -> ()
d_Carrier_914 = erased
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.isEquivalence
d_isEquivalence_916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_916 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_916 v10
du_isEquivalence_916 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_916 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_918 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_918 v10
du_isPartialEquivalence_918 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_918 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.partialSetoid
d_partialSetoid_920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_920 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_920 v10
du_partialSetoid_920 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_920 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1)))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.refl
d_refl_922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny
d_refl_922 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_922 v10
du_refl_922 :: T_IsStrictLeftInverse_852 -> AgdaAny -> AgdaAny
du_refl_922 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v1)))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.reflexive
d_reflexive_924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_924 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_924 v10
du_reflexive_924 ::
  T_IsStrictLeftInverse_852 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_924 v0
  = let v1 = d_isCongruent_864 (coe v0) in
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
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.setoid
d_setoid_926 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_926 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_926 v10
du_setoid_926 ::
  T_IsStrictLeftInverse_852 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_926 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_66
      (coe d_isCongruent_864 (coe v0))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.sym
d_sym_928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_928 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_928 v10
du_sym_928 ::
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_928 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictLeftInverse._._.Eq₂.trans
d_trans_930 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_930 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_930 v10
du_trans_930 ::
  T_IsStrictLeftInverse_852 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_930 v0
  = let v1 = d_isCongruent_864 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictRightInverse
d_IsStrictRightInverse_936 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsStrictRightInverse_936
  = C_IsStrictRightInverse'46'constructor_24625 MAlonzo.Code.Function.Structures.T_IsCongruent_22
                                                (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                (AgdaAny -> AgdaAny)
-- Function.Structures.Biased.IsStrictRightInverse.isCongruent
d_isCongruent_948 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_948 v0
  = case coe v0 of
      C_IsStrictRightInverse'46'constructor_24625 v1 v2 v3 -> coe v1
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictRightInverse.from-cong
d_from'45'cong_950 ::
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_950 v0
  = case coe v0 of
      C_IsStrictRightInverse'46'constructor_24625 v1 v2 v3 -> coe v2
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictRightInverse.strictlyInverseʳ
d_strictlyInverse'691'_952 ::
  T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny
d_strictlyInverse'691'_952 v0
  = case coe v0 of
      C_IsStrictRightInverse'46'constructor_24625 v1 v2 v3 -> coe v3
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictRightInverse.isRightInverse
d_isRightInverse_954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
d_isRightInverse_954 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_isRightInverse_954 v8 v9 v10
du_isRightInverse_954 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
du_isRightInverse_954 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsRightInverse'46'constructor_18837
      (coe d_isCongruent_948 (coe v2)) (coe d_from'45'cong_950 (coe v2))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_strictlyInverse'691''8658'inverse'691'_92
         (coe
            MAlonzo.Code.Function.Structures.du_setoid_40
            (coe d_isCongruent_948 (coe v2)))
         v1 v0 (d_from'45'cong_950 (coe v2))
         (d_strictlyInverse'691'_952 (coe v2)))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁._≈_
d__'8776'__970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny -> ()
d__'8776'__970 = erased
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁._≉_
d__'8777'__972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny -> ()
d__'8777'__972 = erased
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.Carrier
d_Carrier_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsStrictRightInverse_936 -> ()
d_Carrier_974 = erased
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.isEquivalence
d_isEquivalence_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_976 v10
du_isEquivalence_976 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_976 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_978 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_978 v10
du_isPartialEquivalence_978 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_978 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.partialSetoid
d_partialSetoid_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_980 v10
du_partialSetoid_980 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_980 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1)))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.refl
d_refl_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny
d_refl_982 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_982 v10
du_refl_982 :: T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny
du_refl_982 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
            (coe v1)))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.reflexive
d_reflexive_984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_984 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_984 v10
du_reflexive_984 ::
  T_IsStrictRightInverse_936 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_984 v0
  = let v1 = d_isCongruent_948 (coe v0) in
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
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.setoid
d_setoid_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_986 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_986 v10
du_setoid_986 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_986 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_40
      (coe d_isCongruent_948 (coe v0))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.sym
d_sym_988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_988 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_988 v10
du_sym_988 ::
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_988 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₁.trans
d_trans_990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_990 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_990 v10
du_trans_990 ::
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_990 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂._≈_
d__'8776'__994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny -> ()
d__'8776'__994 = erased
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂._≉_
d__'8777'__996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny -> ()
d__'8777'__996 = erased
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.Carrier
d_Carrier_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsStrictRightInverse_936 -> ()
d_Carrier_998 = erased
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.isEquivalence
d_isEquivalence_1000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1000 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_1000 v10
du_isEquivalence_1000 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1000 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_1002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            v10
  = du_isPartialEquivalence_1002 v10
du_isPartialEquivalence_1002 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1002 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.partialSetoid
d_partialSetoid_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_1004 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_1004 v10
du_partialSetoid_1004 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_1004 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1)))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.refl
d_refl_1006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny
d_refl_1006 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_1006 v10
du_refl_1006 :: T_IsStrictRightInverse_936 -> AgdaAny -> AgdaAny
du_refl_1006 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
            (coe v1)))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.reflexive
d_reflexive_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1008 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_1008 v10
du_reflexive_1008 ::
  T_IsStrictRightInverse_936 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1008 v0
  = let v1 = d_isCongruent_948 (coe v0) in
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
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.setoid
d_setoid_1010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1010 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_1010 v10
du_setoid_1010 ::
  T_IsStrictRightInverse_936 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1010 v0
  = coe
      MAlonzo.Code.Function.Structures.du_setoid_66
      (coe d_isCongruent_948 (coe v0))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.sym
d_sym_1012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1012 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_1012 v10
du_sym_1012 ::
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1012 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictRightInverse._._.Eq₂.trans
d_trans_1014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1014 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_1014 v10
du_trans_1014 ::
  T_IsStrictRightInverse_936 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1014 v0
  = let v1 = d_isCongruent_948 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.Biased.IsStrictInverse
d_IsStrictInverse_1020 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsStrictInverse_1020
  = C_IsStrictInverse'46'constructor_28621 MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
                                           (AgdaAny -> AgdaAny)
-- Function.Structures.Biased.IsStrictInverse.isLeftInverse
d_isLeftInverse_1030 ::
  T_IsStrictInverse_1020 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_1030 v0
  = case coe v0 of
      C_IsStrictInverse'46'constructor_28621 v1 v2 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictInverse.strictlyInverseʳ
d_strictlyInverse'691'_1032 ::
  T_IsStrictInverse_1020 -> AgdaAny -> AgdaAny
d_strictlyInverse'691'_1032 v0
  = case coe v0 of
      C_IsStrictInverse'46'constructor_28621 v1 v2 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.Biased.IsStrictInverse.isInverse
d_isInverse_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictInverse_1020 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490
d_isInverse_1034 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_isInverse_1034 v8 v9 v10
du_isInverse_1034 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  T_IsStrictInverse_1020 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490
du_isInverse_1034 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsInverse'46'constructor_22449
      (coe d_isLeftInverse_1030 (coe v2))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_strictlyInverse'691''8658'inverse'691'_92
         (let v3 = d_isLeftInverse_1030 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Function.Structures.du_setoid_40
               (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3))))
         v1 v0
         (MAlonzo.Code.Function.Structures.d_from'45'cong_336
            (coe d_isLeftInverse_1030 (coe v2)))
         (d_strictlyInverse'691'_1032 (coe v2)))
