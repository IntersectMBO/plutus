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

module MAlonzo.Code.Function.Structures where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Structures.IsCongruent
d_IsCongruent_22 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsCongruent_22
  = C_IsCongruent'46'constructor_985 (AgdaAny ->
                                      AgdaAny -> AgdaAny -> AgdaAny)
                                     MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
                                     MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
-- Function.Structures.IsCongruent.cong
d_cong_32 ::
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_32 v0
  = case coe v0 of
      C_IsCongruent'46'constructor_985 v1 v2 v3 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsCongruent.isEquivalence₁
d_isEquivalence'8321'_34 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_34 v0
  = case coe v0 of
      C_IsCongruent'46'constructor_985 v1 v2 v3 -> coe v2
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsCongruent.isEquivalence₂
d_isEquivalence'8322'_36 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_36 v0
  = case coe v0 of
      C_IsCongruent'46'constructor_985 v1 v2 v3 -> coe v3
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsCongruent.Eq₁.setoid
d_setoid_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_40 v9
du_setoid_40 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_40 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (d_isEquivalence'8321'_34 (coe v0))
-- Function.Structures.IsCongruent.Eq₁._._≈_
d__'8776'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> ()
d__'8776'__44 = erased
-- Function.Structures.IsCongruent.Eq₁._._≉_
d__'8777'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> ()
d__'8777'__46 = erased
-- Function.Structures.IsCongruent.Eq₁._.Carrier
d_Carrier_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsCongruent_22 -> ()
d_Carrier_48 = erased
-- Function.Structures.IsCongruent.Eq₁._.isEquivalence
d_isEquivalence_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_50 v9
du_isEquivalence_50 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_50 v0 = coe d_isEquivalence'8321'_34 (coe v0)
-- Function.Structures.IsCongruent.Eq₁._.isPartialEquivalence
d_isPartialEquivalence_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_52 v9
du_isPartialEquivalence_52 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_52 v0
  = let v1 = coe du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.IsCongruent.Eq₁._.partialSetoid
d_partialSetoid_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_54 v9
du_partialSetoid_54 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_54 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
      (coe du_setoid_40 (coe v0))
-- Function.Structures.IsCongruent.Eq₁._.refl
d_refl_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsCongruent_22 -> AgdaAny -> AgdaAny
d_refl_56 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_56 v9
du_refl_56 :: T_IsCongruent_22 -> AgdaAny -> AgdaAny
du_refl_56 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence'8321'_34 (coe v0))
-- Function.Structures.IsCongruent.Eq₁._.reflexive
d_reflexive_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_58 v9
du_reflexive_58 ::
  T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_58 v0
  = let v1 = coe du_setoid_40 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
           v2)
-- Function.Structures.IsCongruent.Eq₁._.sym
d_sym_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_60 v9
du_sym_60 ::
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_60 v0
  = let v1 = coe du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.IsCongruent.Eq₁._.trans
d_trans_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_trans_62 v9
du_trans_62 ::
  T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_62 v0
  = let v1 = coe du_setoid_40 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.IsCongruent.Eq₂.setoid
d_setoid_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_66 v9
du_setoid_66 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_66 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (d_isEquivalence'8322'_36 (coe v0))
-- Function.Structures.IsCongruent.Eq₂._._≈_
d__'8776'__70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> ()
d__'8776'__70 = erased
-- Function.Structures.IsCongruent.Eq₂._._≉_
d__'8777'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> ()
d__'8777'__72 = erased
-- Function.Structures.IsCongruent.Eq₂._.Carrier
d_Carrier_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsCongruent_22 -> ()
d_Carrier_74 = erased
-- Function.Structures.IsCongruent.Eq₂._.isEquivalence
d_isEquivalence_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_76 v9
du_isEquivalence_76 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_76 v0 = coe d_isEquivalence'8322'_36 (coe v0)
-- Function.Structures.IsCongruent.Eq₂._.isPartialEquivalence
d_isPartialEquivalence_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_78 v9
du_isPartialEquivalence_78 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_78 v0
  = let v1 = coe du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.IsCongruent.Eq₂._.partialSetoid
d_partialSetoid_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_80 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_80 v9
du_partialSetoid_80 ::
  T_IsCongruent_22 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_80 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
      (coe du_setoid_66 (coe v0))
-- Function.Structures.IsCongruent.Eq₂._.refl
d_refl_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsCongruent_22 -> AgdaAny -> AgdaAny
d_refl_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_82 v9
du_refl_82 :: T_IsCongruent_22 -> AgdaAny -> AgdaAny
du_refl_82 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe d_isEquivalence'8322'_36 (coe v0))
-- Function.Structures.IsCongruent.Eq₂._.reflexive
d_reflexive_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_84 v9
du_reflexive_84 ::
  T_IsCongruent_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_84 v0
  = let v1 = coe du_setoid_66 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
           v2)
-- Function.Structures.IsCongruent.Eq₂._.sym
d_sym_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_86 v9
du_sym_86 ::
  T_IsCongruent_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_86 v0
  = let v1 = coe du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.IsCongruent.Eq₂._.trans
d_trans_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_trans_88 v9
du_trans_88 ::
  T_IsCongruent_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_88 v0
  = let v1 = coe du_setoid_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Function.Structures.IsInjection
d_IsInjection_92 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsInjection_92
  = C_IsInjection'46'constructor_3997 T_IsCongruent_22
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Structures.IsInjection.isCongruent
d_isCongruent_100 :: T_IsInjection_92 -> T_IsCongruent_22
d_isCongruent_100 v0
  = case coe v0 of
      C_IsInjection'46'constructor_3997 v1 v2 -> coe v1
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsInjection.injective
d_injective_102 ::
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_102 v0
  = case coe v0 of
      C_IsInjection'46'constructor_3997 v1 v2 -> coe v2
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsInjection._.cong
d_cong_106 ::
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_106 v0 = coe d_cong_32 (coe d_isCongruent_100 (coe v0))
-- Function.Structures.IsInjection._.isEquivalence₁
d_isEquivalence'8321'_108 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_108 v0
  = coe d_isEquivalence'8321'_34 (coe d_isCongruent_100 (coe v0))
-- Function.Structures.IsInjection._.isEquivalence₂
d_isEquivalence'8322'_110 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_110 v0
  = coe d_isEquivalence'8322'_36 (coe d_isCongruent_100 (coe v0))
-- Function.Structures.IsInjection._.Eq₁._≈_
d__'8776'__114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> ()
d__'8776'__114 = erased
-- Function.Structures.IsInjection._.Eq₁._≉_
d__'8777'__116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> ()
d__'8777'__116 = erased
-- Function.Structures.IsInjection._.Eq₁.Carrier
d_Carrier_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsInjection_92 -> ()
d_Carrier_118 = erased
-- Function.Structures.IsInjection._.Eq₁.isEquivalence
d_isEquivalence_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_120 v9
du_isEquivalence_120 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_120 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe (coe d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.IsInjection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_122 v9
du_isPartialEquivalence_122 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_122 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsInjection._.Eq₁.partialSetoid
d_partialSetoid_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_124 v9
du_partialSetoid_124 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_124 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_40 (coe v1)))
-- Function.Structures.IsInjection._.Eq₁.refl
d_refl_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsInjection_92 -> AgdaAny -> AgdaAny
d_refl_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_126 v9
du_refl_126 :: T_IsInjection_92 -> AgdaAny -> AgdaAny
du_refl_126 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8321'_34 (coe v1)))
-- Function.Structures.IsInjection._.Eq₁.reflexive
d_reflexive_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_128 v9
du_reflexive_128 ::
  T_IsInjection_92 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_128 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsInjection._.Eq₁.setoid
d_setoid_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_130 v9
du_setoid_130 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_130 v0
  = coe du_setoid_40 (coe d_isCongruent_100 (coe v0))
-- Function.Structures.IsInjection._.Eq₁.sym
d_sym_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_132 v9
du_sym_132 ::
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_132 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsInjection._.Eq₁.trans
d_trans_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_134 v9
du_trans_134 ::
  T_IsInjection_92 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_134 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsInjection._.Eq₂._≈_
d__'8776'__138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> ()
d__'8776'__138 = erased
-- Function.Structures.IsInjection._.Eq₂._≉_
d__'8777'__140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> ()
d__'8777'__140 = erased
-- Function.Structures.IsInjection._.Eq₂.Carrier
d_Carrier_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsInjection_92 -> ()
d_Carrier_142 = erased
-- Function.Structures.IsInjection._.Eq₂.isEquivalence
d_isEquivalence_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_144 v9
du_isEquivalence_144 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_144 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe (coe d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.IsInjection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_146 v9
du_isPartialEquivalence_146 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_146 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsInjection._.Eq₂.partialSetoid
d_partialSetoid_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_148 v9
du_partialSetoid_148 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_148 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_66 (coe v1)))
-- Function.Structures.IsInjection._.Eq₂.refl
d_refl_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsInjection_92 -> AgdaAny -> AgdaAny
d_refl_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_150 v9
du_refl_150 :: T_IsInjection_92 -> AgdaAny -> AgdaAny
du_refl_150 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8322'_36 (coe v1)))
-- Function.Structures.IsInjection._.Eq₂.reflexive
d_reflexive_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_152 v9
du_reflexive_152 ::
  T_IsInjection_92 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_152 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsInjection._.Eq₂.setoid
d_setoid_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_154 v9
du_setoid_154 ::
  T_IsInjection_92 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_154 v0
  = coe du_setoid_66 (coe d_isCongruent_100 (coe v0))
-- Function.Structures.IsInjection._.Eq₂.sym
d_sym_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_156 v9
du_sym_156 ::
  T_IsInjection_92 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_156 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsInjection._.Eq₂.trans
d_trans_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsInjection_92 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_158 v9
du_trans_158 ::
  T_IsInjection_92 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_158 v0
  = let v1 = d_isCongruent_100 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsSurjection
d_IsSurjection_162 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsSurjection_162
  = C_IsSurjection'46'constructor_6463 T_IsCongruent_22
                                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Function.Structures.IsSurjection.isCongruent
d_isCongruent_170 :: T_IsSurjection_162 -> T_IsCongruent_22
d_isCongruent_170 v0
  = case coe v0 of
      C_IsSurjection'46'constructor_6463 v1 v2 -> coe v1
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsSurjection.surjective
d_surjective_172 ::
  T_IsSurjection_162 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_172 v0
  = case coe v0 of
      C_IsSurjection'46'constructor_6463 v1 v2 -> coe v2
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsSurjection._.cong
d_cong_176 ::
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_176 v0 = coe d_cong_32 (coe d_isCongruent_170 (coe v0))
-- Function.Structures.IsSurjection._.isEquivalence₁
d_isEquivalence'8321'_178 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_178 v0
  = coe d_isEquivalence'8321'_34 (coe d_isCongruent_170 (coe v0))
-- Function.Structures.IsSurjection._.isEquivalence₂
d_isEquivalence'8322'_180 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_180 v0
  = coe d_isEquivalence'8322'_36 (coe d_isCongruent_170 (coe v0))
-- Function.Structures.IsSurjection._.Eq₁._≈_
d__'8776'__184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> ()
d__'8776'__184 = erased
-- Function.Structures.IsSurjection._.Eq₁._≉_
d__'8777'__186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> ()
d__'8777'__186 = erased
-- Function.Structures.IsSurjection._.Eq₁.Carrier
d_Carrier_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsSurjection_162 -> ()
d_Carrier_188 = erased
-- Function.Structures.IsSurjection._.Eq₁.isEquivalence
d_isEquivalence_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_190 v9
du_isEquivalence_190 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_190 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe (coe d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.IsSurjection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_192 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_192 v9
du_isPartialEquivalence_192 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_192 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsSurjection._.Eq₁.partialSetoid
d_partialSetoid_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_194 v9
du_partialSetoid_194 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_194 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_40 (coe v1)))
-- Function.Structures.IsSurjection._.Eq₁.refl
d_refl_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsSurjection_162 -> AgdaAny -> AgdaAny
d_refl_196 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_196 v9
du_refl_196 :: T_IsSurjection_162 -> AgdaAny -> AgdaAny
du_refl_196 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8321'_34 (coe v1)))
-- Function.Structures.IsSurjection._.Eq₁.reflexive
d_reflexive_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_198 v9
du_reflexive_198 ::
  T_IsSurjection_162 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_198 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsSurjection._.Eq₁.setoid
d_setoid_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_200 v9
du_setoid_200 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_200 v0
  = coe du_setoid_40 (coe d_isCongruent_170 (coe v0))
-- Function.Structures.IsSurjection._.Eq₁.sym
d_sym_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_202 v9
du_sym_202 ::
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_202 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsSurjection._.Eq₁.trans
d_trans_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_204 v9
du_trans_204 ::
  T_IsSurjection_162 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_204 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsSurjection._.Eq₂._≈_
d__'8776'__208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> ()
d__'8776'__208 = erased
-- Function.Structures.IsSurjection._.Eq₂._≉_
d__'8777'__210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> ()
d__'8777'__210 = erased
-- Function.Structures.IsSurjection._.Eq₂.Carrier
d_Carrier_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsSurjection_162 -> ()
d_Carrier_212 = erased
-- Function.Structures.IsSurjection._.Eq₂.isEquivalence
d_isEquivalence_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_214 v9
du_isEquivalence_214 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_214 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe (coe d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.IsSurjection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_216 v9
du_isPartialEquivalence_216 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_216 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsSurjection._.Eq₂.partialSetoid
d_partialSetoid_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_218 v9
du_partialSetoid_218 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_218 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_66 (coe v1)))
-- Function.Structures.IsSurjection._.Eq₂.refl
d_refl_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsSurjection_162 -> AgdaAny -> AgdaAny
d_refl_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_220 v9
du_refl_220 :: T_IsSurjection_162 -> AgdaAny -> AgdaAny
du_refl_220 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8322'_36 (coe v1)))
-- Function.Structures.IsSurjection._.Eq₂.reflexive
d_reflexive_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_222 v9
du_reflexive_222 ::
  T_IsSurjection_162 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_222 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsSurjection._.Eq₂.setoid
d_setoid_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_224 v9
du_setoid_224 ::
  T_IsSurjection_162 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_224 v0
  = coe du_setoid_66 (coe d_isCongruent_170 (coe v0))
-- Function.Structures.IsSurjection._.Eq₂.sym
d_sym_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_226 v9
du_sym_226 ::
  T_IsSurjection_162 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_226 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsSurjection._.Eq₂.trans
d_trans_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_228 v9
du_trans_228 ::
  T_IsSurjection_162 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_228 v0
  = let v1 = d_isCongruent_170 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsSurjection.strictlySurjective
d_strictlySurjective_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSurjection_162 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_strictlySurjective_230 v9 v10
du_strictlySurjective_230 ::
  T_IsSurjection_162 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective_230 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_map'8322'_150
      (\ v2 v3 ->
         coe
           v3 v2
           (coe
              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
              (d_isEquivalence'8321'_34 (coe d_isCongruent_170 (coe v0))) v2))
      (coe d_surjective_172 v0 v1)
-- Function.Structures.IsBijection
d_IsBijection_238 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsBijection_238
  = C_IsBijection'46'constructor_10113 T_IsInjection_92
                                       (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Function.Structures.IsBijection.isInjection
d_isInjection_246 :: T_IsBijection_238 -> T_IsInjection_92
d_isInjection_246 v0
  = case coe v0 of
      C_IsBijection'46'constructor_10113 v1 v2 -> coe v1
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBijection.surjective
d_surjective_248 ::
  T_IsBijection_238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_248 v0
  = case coe v0 of
      C_IsBijection'46'constructor_10113 v1 v2 -> coe v2
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBijection._.cong
d_cong_252 ::
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_252 v0
  = coe
      d_cong_32 (coe d_isCongruent_100 (coe d_isInjection_246 (coe v0)))
-- Function.Structures.IsBijection._.injective
d_injective_254 ::
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_254 v0
  = coe d_injective_102 (coe d_isInjection_246 (coe v0))
-- Function.Structures.IsBijection._.isCongruent
d_isCongruent_256 :: T_IsBijection_238 -> T_IsCongruent_22
d_isCongruent_256 v0
  = coe d_isCongruent_100 (coe d_isInjection_246 (coe v0))
-- Function.Structures.IsBijection._.isEquivalence₁
d_isEquivalence'8321'_258 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_258 v0
  = coe
      d_isEquivalence'8321'_34
      (coe d_isCongruent_100 (coe d_isInjection_246 (coe v0)))
-- Function.Structures.IsBijection._.isEquivalence₂
d_isEquivalence'8322'_260 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_260 v0
  = coe
      d_isEquivalence'8322'_36
      (coe d_isCongruent_100 (coe d_isInjection_246 (coe v0)))
-- Function.Structures.IsBijection._.Eq₁._≈_
d__'8776'__264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> ()
d__'8776'__264 = erased
-- Function.Structures.IsBijection._.Eq₁._≉_
d__'8777'__266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> ()
d__'8777'__266 = erased
-- Function.Structures.IsBijection._.Eq₁.Carrier
d_Carrier_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsBijection_238 -> ()
d_Carrier_268 = erased
-- Function.Structures.IsBijection._.Eq₁.isEquivalence
d_isEquivalence_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_270 v9
du_isEquivalence_270 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_270 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe (coe d_isEquivalence'8321'_34 (coe v2)))
-- Function.Structures.IsBijection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_272 v9
du_isPartialEquivalence_272 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_272 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsBijection._.Eq₁.partialSetoid
d_partialSetoid_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_274 v9
du_partialSetoid_274 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_274 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe du_setoid_40 (coe v2))))
-- Function.Structures.IsBijection._.Eq₁.refl
d_refl_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsBijection_238 -> AgdaAny -> AgdaAny
d_refl_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_276 v9
du_refl_276 :: T_IsBijection_238 -> AgdaAny -> AgdaAny
du_refl_276 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe d_isEquivalence'8321'_34 (coe v2))))
-- Function.Structures.IsBijection._.Eq₁.reflexive
d_reflexive_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_278 v9
du_reflexive_278 ::
  T_IsBijection_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_278 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Structures.IsBijection._.Eq₁.setoid
d_setoid_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_280 v9
du_setoid_280 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_280 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe (coe du_setoid_40 (coe d_isCongruent_100 (coe v1)))
-- Function.Structures.IsBijection._.Eq₁.sym
d_sym_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_282 v9
du_sym_282 ::
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_282 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsBijection._.Eq₁.trans
d_trans_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_284 v9
du_trans_284 ::
  T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_284 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsBijection._.Eq₂._≈_
d__'8776'__288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> ()
d__'8776'__288 = erased
-- Function.Structures.IsBijection._.Eq₂._≉_
d__'8777'__290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> ()
d__'8777'__290 = erased
-- Function.Structures.IsBijection._.Eq₂.Carrier
d_Carrier_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsBijection_238 -> ()
d_Carrier_292 = erased
-- Function.Structures.IsBijection._.Eq₂.isEquivalence
d_isEquivalence_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_294 v9
du_isEquivalence_294 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_294 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe (coe d_isEquivalence'8322'_36 (coe v2)))
-- Function.Structures.IsBijection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_296 v9
du_isPartialEquivalence_296 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_296 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsBijection._.Eq₂.partialSetoid
d_partialSetoid_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_298 v9
du_partialSetoid_298 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_298 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe du_setoid_66 (coe v2))))
-- Function.Structures.IsBijection._.Eq₂.refl
d_refl_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsBijection_238 -> AgdaAny -> AgdaAny
d_refl_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_300 v9
du_refl_300 :: T_IsBijection_238 -> AgdaAny -> AgdaAny
du_refl_300 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe d_isEquivalence'8322'_36 (coe v2))))
-- Function.Structures.IsBijection._.Eq₂.reflexive
d_reflexive_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_302 v9
du_reflexive_302 ::
  T_IsBijection_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_302 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Structures.IsBijection._.Eq₂.setoid
d_setoid_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_304 v9
du_setoid_304 ::
  T_IsBijection_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_304 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe (coe du_setoid_66 (coe d_isCongruent_100 (coe v1)))
-- Function.Structures.IsBijection._.Eq₂.sym
d_sym_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_306 v9
du_sym_306 ::
  T_IsBijection_238 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_306 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsBijection._.Eq₂.trans
d_trans_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_308 v9
du_trans_308 ::
  T_IsBijection_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_308 v0
  = let v1 = d_isInjection_246 (coe v0) in
    coe
      (let v2 = d_isCongruent_100 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsBijection.bijective
d_bijective_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bijective_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_bijective_310 v9
du_bijective_310 ::
  T_IsBijection_238 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bijective_310 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_injective_102 (coe d_isInjection_246 (coe v0)))
      (coe d_surjective_248 (coe v0))
-- Function.Structures.IsBijection.isSurjection
d_isSurjection_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsBijection_238 -> T_IsSurjection_162
d_isSurjection_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSurjection_312 v9
du_isSurjection_312 :: T_IsBijection_238 -> T_IsSurjection_162
du_isSurjection_312 v0
  = coe
      C_IsSurjection'46'constructor_6463
      (coe d_isCongruent_100 (coe d_isInjection_246 (coe v0)))
      (coe d_surjective_248 (coe v0))
-- Function.Structures.IsBijection._.strictlySurjective
d_strictlySurjective_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsBijection_238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_strictlySurjective_316 v9
du_strictlySurjective_316 ::
  T_IsBijection_238 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective_316 v0
  = coe du_strictlySurjective_230 (coe du_isSurjection_312 (coe v0))
-- Function.Structures.IsLeftInverse
d_IsLeftInverse_322 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsLeftInverse_322
  = C_IsLeftInverse'46'constructor_14363 T_IsCongruent_22
                                         (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                         (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Structures.IsLeftInverse.isCongruent
d_isCongruent_334 :: T_IsLeftInverse_322 -> T_IsCongruent_22
d_isCongruent_334 v0
  = case coe v0 of
      C_IsLeftInverse'46'constructor_14363 v1 v2 v3 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsLeftInverse.from-cong
d_from'45'cong_336 ::
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_336 v0
  = case coe v0 of
      C_IsLeftInverse'46'constructor_14363 v1 v2 v3 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsLeftInverse.inverseˡ
d_inverse'737'_338 ::
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_338 v0
  = case coe v0 of
      C_IsLeftInverse'46'constructor_14363 v1 v2 v3 -> coe v3
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsLeftInverse._.isEquivalence₁
d_isEquivalence'8321'_342 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_342 v0
  = coe d_isEquivalence'8321'_34 (coe d_isCongruent_334 (coe v0))
-- Function.Structures.IsLeftInverse._.isEquivalence₂
d_isEquivalence'8322'_344 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_344 v0
  = coe d_isEquivalence'8322'_36 (coe d_isCongruent_334 (coe v0))
-- Function.Structures.IsLeftInverse._.cong
d_cong_346 ::
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_346 v0 = coe d_cong_32 (coe d_isCongruent_334 (coe v0))
-- Function.Structures.IsLeftInverse._.Eq₁._≈_
d__'8776'__350 ::
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
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> ()
d__'8776'__350 = erased
-- Function.Structures.IsLeftInverse._.Eq₁._≉_
d__'8777'__352 ::
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
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> ()
d__'8777'__352 = erased
-- Function.Structures.IsLeftInverse._.Eq₁.Carrier
d_Carrier_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsLeftInverse_322 -> ()
d_Carrier_354 = erased
-- Function.Structures.IsLeftInverse._.Eq₁.isEquivalence
d_isEquivalence_356 ::
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
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_356 v10
du_isEquivalence_356 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_356 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe (coe d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.IsLeftInverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_358 ::
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
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_358 v10
du_isPartialEquivalence_358 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_358 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsLeftInverse._.Eq₁.partialSetoid
d_partialSetoid_360 ::
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
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_360 v10
du_partialSetoid_360 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_360 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_40 (coe v1)))
-- Function.Structures.IsLeftInverse._.Eq₁.refl
d_refl_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsLeftInverse_322 -> AgdaAny -> AgdaAny
d_refl_362 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_362 v10
du_refl_362 :: T_IsLeftInverse_322 -> AgdaAny -> AgdaAny
du_refl_362 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8321'_34 (coe v1)))
-- Function.Structures.IsLeftInverse._.Eq₁.reflexive
d_reflexive_364 ::
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
  T_IsLeftInverse_322 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_364 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_364 v10
du_reflexive_364 ::
  T_IsLeftInverse_322 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_364 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsLeftInverse._.Eq₁.setoid
d_setoid_366 ::
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
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_366 v10
du_setoid_366 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_366 v0
  = coe du_setoid_40 (coe d_isCongruent_334 (coe v0))
-- Function.Structures.IsLeftInverse._.Eq₁.sym
d_sym_368 ::
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
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_368 v10
du_sym_368 ::
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_368 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsLeftInverse._.Eq₁.trans
d_trans_370 ::
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
  T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_370 v10
du_trans_370 ::
  T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_370 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsLeftInverse._.Eq₂._≈_
d__'8776'__374 ::
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
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> ()
d__'8776'__374 = erased
-- Function.Structures.IsLeftInverse._.Eq₂._≉_
d__'8777'__376 ::
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
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> ()
d__'8777'__376 = erased
-- Function.Structures.IsLeftInverse._.Eq₂.Carrier
d_Carrier_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsLeftInverse_322 -> ()
d_Carrier_378 = erased
-- Function.Structures.IsLeftInverse._.Eq₂.isEquivalence
d_isEquivalence_380 ::
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
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_380 v10
du_isEquivalence_380 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_380 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe (coe d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.IsLeftInverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_382 ::
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
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_382 v10
du_isPartialEquivalence_382 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_382 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsLeftInverse._.Eq₂.partialSetoid
d_partialSetoid_384 ::
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
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_384 v10
du_partialSetoid_384 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_384 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_66 (coe v1)))
-- Function.Structures.IsLeftInverse._.Eq₂.refl
d_refl_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsLeftInverse_322 -> AgdaAny -> AgdaAny
d_refl_386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_386 v10
du_refl_386 :: T_IsLeftInverse_322 -> AgdaAny -> AgdaAny
du_refl_386 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8322'_36 (coe v1)))
-- Function.Structures.IsLeftInverse._.Eq₂.reflexive
d_reflexive_388 ::
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
  T_IsLeftInverse_322 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_388 v10
du_reflexive_388 ::
  T_IsLeftInverse_322 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_388 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsLeftInverse._.Eq₂.setoid
d_setoid_390 ::
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
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_390 v10
du_setoid_390 ::
  T_IsLeftInverse_322 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_390 v0
  = coe du_setoid_66 (coe d_isCongruent_334 (coe v0))
-- Function.Structures.IsLeftInverse._.Eq₂.sym
d_sym_392 ::
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
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_392 v10
du_sym_392 ::
  T_IsLeftInverse_322 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_392 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsLeftInverse._.Eq₂.trans
d_trans_394 ::
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
  T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_394 v10
du_trans_394 ::
  T_IsLeftInverse_322 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_394 v0
  = let v1 = d_isCongruent_334 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsLeftInverse.strictlyInverseˡ
d_strictlyInverse'737'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsLeftInverse_322 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                           v10 v11
  = du_strictlyInverse'737'_396 v9 v10 v11
du_strictlyInverse'737'_396 ::
  (AgdaAny -> AgdaAny) -> T_IsLeftInverse_322 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_396 v0 v1 v2
  = coe
      d_inverse'737'_338 v1 v2 (coe v0 v2)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (d_isEquivalence'8321'_34 (coe d_isCongruent_334 (coe v1)))
         (coe v0 v2))
-- Function.Structures.IsLeftInverse.isSurjection
d_isSurjection_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsLeftInverse_322 -> T_IsSurjection_162
d_isSurjection_400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_isSurjection_400 v9 v10
du_isSurjection_400 ::
  (AgdaAny -> AgdaAny) -> T_IsLeftInverse_322 -> T_IsSurjection_162
du_isSurjection_400 v0 v1
  = coe
      C_IsSurjection'46'constructor_6463 (coe d_isCongruent_334 (coe v1))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v2)
              (coe d_inverse'737'_338 v1 v2)))
-- Function.Structures.IsRightInverse
d_IsRightInverse_408 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsRightInverse_408
  = C_IsRightInverse'46'constructor_18837 T_IsCongruent_22
                                          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Structures.IsRightInverse.isCongruent
d_isCongruent_420 :: T_IsRightInverse_408 -> T_IsCongruent_22
d_isCongruent_420 v0
  = case coe v0 of
      C_IsRightInverse'46'constructor_18837 v1 v2 v3 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsRightInverse.from-cong
d_from'45'cong_422 ::
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_422 v0
  = case coe v0 of
      C_IsRightInverse'46'constructor_18837 v1 v2 v3 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsRightInverse.inverseʳ
d_inverse'691'_424 ::
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_424 v0
  = case coe v0 of
      C_IsRightInverse'46'constructor_18837 v1 v2 v3 -> coe v3
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsRightInverse._.isEquivalence₁
d_isEquivalence'8321'_428 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_428 v0
  = coe d_isEquivalence'8321'_34 (coe d_isCongruent_420 (coe v0))
-- Function.Structures.IsRightInverse._.isEquivalence₂
d_isEquivalence'8322'_430 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_430 v0
  = coe d_isEquivalence'8322'_36 (coe d_isCongruent_420 (coe v0))
-- Function.Structures.IsRightInverse._.cong
d_cong_432 ::
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_432 v0 = coe d_cong_32 (coe d_isCongruent_420 (coe v0))
-- Function.Structures.IsRightInverse._.Eq₁._≈_
d__'8776'__436 ::
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
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> ()
d__'8776'__436 = erased
-- Function.Structures.IsRightInverse._.Eq₁._≉_
d__'8777'__438 ::
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
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> ()
d__'8777'__438 = erased
-- Function.Structures.IsRightInverse._.Eq₁.Carrier
d_Carrier_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsRightInverse_408 -> ()
d_Carrier_440 = erased
-- Function.Structures.IsRightInverse._.Eq₁.isEquivalence
d_isEquivalence_442 ::
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
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_442 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_442 v10
du_isEquivalence_442 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_442 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe (coe d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.IsRightInverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_444 ::
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
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_444 v10
du_isPartialEquivalence_444 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_444 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsRightInverse._.Eq₁.partialSetoid
d_partialSetoid_446 ::
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
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_446 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_446 v10
du_partialSetoid_446 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_446 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_40 (coe v1)))
-- Function.Structures.IsRightInverse._.Eq₁.refl
d_refl_448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsRightInverse_408 -> AgdaAny -> AgdaAny
d_refl_448 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_448 v10
du_refl_448 :: T_IsRightInverse_408 -> AgdaAny -> AgdaAny
du_refl_448 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8321'_34 (coe v1)))
-- Function.Structures.IsRightInverse._.Eq₁.reflexive
d_reflexive_450 ::
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
  T_IsRightInverse_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_450 v10
du_reflexive_450 ::
  T_IsRightInverse_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_450 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsRightInverse._.Eq₁.setoid
d_setoid_452 ::
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
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_452 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_452 v10
du_setoid_452 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_452 v0
  = coe du_setoid_40 (coe d_isCongruent_420 (coe v0))
-- Function.Structures.IsRightInverse._.Eq₁.sym
d_sym_454 ::
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
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_454 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_454 v10
du_sym_454 ::
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_454 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsRightInverse._.Eq₁.trans
d_trans_456 ::
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
  T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_456 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_456 v10
du_trans_456 ::
  T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_456 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsRightInverse._.Eq₂._≈_
d__'8776'__460 ::
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
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> ()
d__'8776'__460 = erased
-- Function.Structures.IsRightInverse._.Eq₂._≉_
d__'8777'__462 ::
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
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> ()
d__'8777'__462 = erased
-- Function.Structures.IsRightInverse._.Eq₂.Carrier
d_Carrier_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsRightInverse_408 -> ()
d_Carrier_464 = erased
-- Function.Structures.IsRightInverse._.Eq₂.isEquivalence
d_isEquivalence_466 ::
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
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_466 v10
du_isEquivalence_466 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_466 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe (coe d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.IsRightInverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_468 ::
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
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_468 v10
du_isPartialEquivalence_468 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_468 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsRightInverse._.Eq₂.partialSetoid
d_partialSetoid_470 ::
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
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_470 v10
du_partialSetoid_470 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_470 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_66 (coe v1)))
-- Function.Structures.IsRightInverse._.Eq₂.refl
d_refl_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsRightInverse_408 -> AgdaAny -> AgdaAny
d_refl_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_472 v10
du_refl_472 :: T_IsRightInverse_408 -> AgdaAny -> AgdaAny
du_refl_472 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8322'_36 (coe v1)))
-- Function.Structures.IsRightInverse._.Eq₂.reflexive
d_reflexive_474 ::
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
  T_IsRightInverse_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_474 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_474 v10
du_reflexive_474 ::
  T_IsRightInverse_408 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_474 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsRightInverse._.Eq₂.setoid
d_setoid_476 ::
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
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_476 v10
du_setoid_476 ::
  T_IsRightInverse_408 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_476 v0
  = coe du_setoid_66 (coe d_isCongruent_420 (coe v0))
-- Function.Structures.IsRightInverse._.Eq₂.sym
d_sym_478 ::
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
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_478 v10
du_sym_478 ::
  T_IsRightInverse_408 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_478 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsRightInverse._.Eq₂.trans
d_trans_480 ::
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
  T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_480 v10
du_trans_480 ::
  T_IsRightInverse_408 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_480 v0
  = let v1 = d_isCongruent_420 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsRightInverse.strictlyInverseʳ
d_strictlyInverse'691'_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsRightInverse_408 -> AgdaAny -> AgdaAny
d_strictlyInverse'691'_482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                           v10 v11
  = du_strictlyInverse'691'_482 v8 v10 v11
du_strictlyInverse'691'_482 ::
  (AgdaAny -> AgdaAny) -> T_IsRightInverse_408 -> AgdaAny -> AgdaAny
du_strictlyInverse'691'_482 v0 v1 v2
  = coe
      d_inverse'691'_424 v1 v2 (coe v0 v2)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (d_isEquivalence'8322'_36 (coe d_isCongruent_420 (coe v1)))
         (coe v0 v2))
-- Function.Structures.IsInverse
d_IsInverse_490 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsInverse_490
  = C_IsInverse'46'constructor_22449 T_IsLeftInverse_322
                                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Structures.IsInverse.isLeftInverse
d_isLeftInverse_500 :: T_IsInverse_490 -> T_IsLeftInverse_322
d_isLeftInverse_500 v0
  = case coe v0 of
      C_IsInverse'46'constructor_22449 v1 v2 -> coe v1
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsInverse.inverseʳ
d_inverse'691'_502 ::
  T_IsInverse_490 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_502 v0
  = case coe v0 of
      C_IsInverse'46'constructor_22449 v1 v2 -> coe v2
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsInverse._.from-cong
d_from'45'cong_506 ::
  T_IsInverse_490 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_506 v0
  = coe d_from'45'cong_336 (coe d_isLeftInverse_500 (coe v0))
-- Function.Structures.IsInverse._.inverseˡ
d_inverse'737'_508 ::
  T_IsInverse_490 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_508 v0
  = coe d_inverse'737'_338 (coe d_isLeftInverse_500 (coe v0))
-- Function.Structures.IsInverse._.isCongruent
d_isCongruent_510 :: T_IsInverse_490 -> T_IsCongruent_22
d_isCongruent_510 v0
  = coe d_isCongruent_334 (coe d_isLeftInverse_500 (coe v0))
-- Function.Structures.IsInverse._.isEquivalence₁
d_isEquivalence'8321'_512 ::
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_512 v0
  = coe
      d_isEquivalence'8321'_34
      (coe d_isCongruent_334 (coe d_isLeftInverse_500 (coe v0)))
-- Function.Structures.IsInverse._.isEquivalence₂
d_isEquivalence'8322'_514 ::
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_514 v0
  = coe
      d_isEquivalence'8322'_36
      (coe d_isCongruent_334 (coe d_isLeftInverse_500 (coe v0)))
-- Function.Structures.IsInverse._.isSurjection
d_isSurjection_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> T_IsSurjection_162
d_isSurjection_516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_isSurjection_516 v9 v10
du_isSurjection_516 ::
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> T_IsSurjection_162
du_isSurjection_516 v0 v1
  = coe
      du_isSurjection_400 (coe v0) (coe d_isLeftInverse_500 (coe v1))
-- Function.Structures.IsInverse._.strictlyInverseˡ
d_strictlyInverse'737'_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                           v10
  = du_strictlyInverse'737'_518 v9 v10
du_strictlyInverse'737'_518 ::
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_518 v0 v1
  = coe
      du_strictlyInverse'737'_396 (coe v0)
      (coe d_isLeftInverse_500 (coe v1))
-- Function.Structures.IsInverse._.cong
d_cong_520 ::
  T_IsInverse_490 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_520 v0
  = coe
      d_cong_32
      (coe d_isCongruent_334 (coe d_isLeftInverse_500 (coe v0)))
-- Function.Structures.IsInverse._.Eq₁._≈_
d__'8776'__524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny -> ()
d__'8776'__524 = erased
-- Function.Structures.IsInverse._.Eq₁._≉_
d__'8777'__526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny -> ()
d__'8777'__526 = erased
-- Function.Structures.IsInverse._.Eq₁.Carrier
d_Carrier_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> ()
d_Carrier_528 = erased
-- Function.Structures.IsInverse._.Eq₁.isEquivalence
d_isEquivalence_530 ::
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
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_530 v10
du_isEquivalence_530 ::
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_530 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe (coe d_isEquivalence'8321'_34 (coe v2)))
-- Function.Structures.IsInverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_532 ::
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
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_532 v10
du_isPartialEquivalence_532 ::
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_532 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsInverse._.Eq₁.partialSetoid
d_partialSetoid_534 ::
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
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_534 v10
du_partialSetoid_534 ::
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_534 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe du_setoid_40 (coe v2))))
-- Function.Structures.IsInverse._.Eq₁.refl
d_refl_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny
d_refl_536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_536 v10
du_refl_536 :: T_IsInverse_490 -> AgdaAny -> AgdaAny
du_refl_536 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe d_isEquivalence'8321'_34 (coe v2))))
-- Function.Structures.IsInverse._.Eq₁.reflexive
d_reflexive_538 ::
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
  T_IsInverse_490 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_538 v10
du_reflexive_538 ::
  T_IsInverse_490 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_538 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Structures.IsInverse._.Eq₁.setoid
d_setoid_540 ::
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
  T_IsInverse_490 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_540 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_540 v10
du_setoid_540 ::
  T_IsInverse_490 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_540 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe (coe du_setoid_40 (coe d_isCongruent_334 (coe v1)))
-- Function.Structures.IsInverse._.Eq₁.sym
d_sym_542 ::
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
  T_IsInverse_490 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_542 v10
du_sym_542 ::
  T_IsInverse_490 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_542 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsInverse._.Eq₁.trans
d_trans_544 ::
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
  T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_544 v10
du_trans_544 ::
  T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_544 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsInverse._.Eq₂._≈_
d__'8776'__548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny -> ()
d__'8776'__548 = erased
-- Function.Structures.IsInverse._.Eq₂._≉_
d__'8777'__550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny -> ()
d__'8777'__550 = erased
-- Function.Structures.IsInverse._.Eq₂.Carrier
d_Carrier_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> ()
d_Carrier_552 = erased
-- Function.Structures.IsInverse._.Eq₂.isEquivalence
d_isEquivalence_554 ::
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
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isEquivalence_554 v10
du_isEquivalence_554 ::
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_554 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe (coe d_isEquivalence'8322'_36 (coe v2)))
-- Function.Structures.IsInverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_556 ::
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
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_556 v10
du_isPartialEquivalence_556 ::
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_556 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsInverse._.Eq₂.partialSetoid
d_partialSetoid_558 ::
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
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_558 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_partialSetoid_558 v10
du_partialSetoid_558 ::
  T_IsInverse_490 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_558 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe du_setoid_66 (coe v2))))
-- Function.Structures.IsInverse._.Eq₂.refl
d_refl_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny
d_refl_560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_560 v10
du_refl_560 :: T_IsInverse_490 -> AgdaAny -> AgdaAny
du_refl_560 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe d_isEquivalence'8322'_36 (coe v2))))
-- Function.Structures.IsInverse._.Eq₂.reflexive
d_reflexive_562 ::
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
  T_IsInverse_490 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_562 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_562 v10
du_reflexive_562 ::
  T_IsInverse_490 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_562 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Structures.IsInverse._.Eq₂.setoid
d_setoid_564 ::
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
  T_IsInverse_490 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_setoid_564 v10
du_setoid_564 ::
  T_IsInverse_490 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_564 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe (coe du_setoid_66 (coe d_isCongruent_334 (coe v1)))
-- Function.Structures.IsInverse._.Eq₂.sym
d_sym_566 ::
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
  T_IsInverse_490 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_sym_566 v10
du_sym_566 ::
  T_IsInverse_490 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_566 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsInverse._.Eq₂.trans
d_trans_568 ::
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
  T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_trans_568 v10
du_trans_568 ::
  T_IsInverse_490 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_568 v0
  = let v1 = d_isLeftInverse_500 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsInverse.isRightInverse
d_isRightInverse_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> T_IsRightInverse_408
d_isRightInverse_570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isRightInverse_570 v10
du_isRightInverse_570 :: T_IsInverse_490 -> T_IsRightInverse_408
du_isRightInverse_570 v0
  = coe
      C_IsRightInverse'46'constructor_18837
      (coe d_isCongruent_334 (coe d_isLeftInverse_500 (coe v0)))
      (coe d_from'45'cong_336 (coe d_isLeftInverse_500 (coe v0)))
      (coe d_inverse'691'_502 (coe v0))
-- Function.Structures.IsInverse._.strictlyInverseʳ
d_strictlyInverse'691'_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny
d_strictlyInverse'691'_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
                           v10
  = du_strictlyInverse'691'_574 v8 v10
du_strictlyInverse'691'_574 ::
  (AgdaAny -> AgdaAny) -> T_IsInverse_490 -> AgdaAny -> AgdaAny
du_strictlyInverse'691'_574 v0 v1
  = coe
      du_strictlyInverse'691'_482 (coe v0)
      (coe du_isRightInverse_570 (coe v1))
-- Function.Structures.IsInverse.inverse
d_inverse_576 ::
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
  T_IsInverse_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_inverse_576 v10
du_inverse_576 ::
  T_IsInverse_490 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_576 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_inverse'737'_338 (coe d_isLeftInverse_500 (coe v0)))
      (coe d_inverse'691'_502 (coe v0))
-- Function.Structures.IsBiEquivalence
d_IsBiEquivalence_584 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_IsBiEquivalence_584
  = C_IsBiEquivalence'46'constructor_28009 T_IsCongruent_22
                                           (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                           (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Structures.IsBiEquivalence.to-isCongruent
d_to'45'isCongruent_598 ::
  T_IsBiEquivalence_584 -> T_IsCongruent_22
d_to'45'isCongruent_598 v0
  = case coe v0 of
      C_IsBiEquivalence'46'constructor_28009 v1 v2 v3 -> coe v1
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBiEquivalence.from₁-cong
d_from'8321''45'cong_600 ::
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8321''45'cong_600 v0
  = case coe v0 of
      C_IsBiEquivalence'46'constructor_28009 v1 v2 v3 -> coe v2
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBiEquivalence.from₂-cong
d_from'8322''45'cong_602 ::
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8322''45'cong_602 v0
  = case coe v0 of
      C_IsBiEquivalence'46'constructor_28009 v1 v2 v3 -> coe v3
      _                                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBiEquivalence._.isEquivalence₁
d_isEquivalence'8321'_606 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_606 v0
  = coe
      d_isEquivalence'8321'_34 (coe d_to'45'isCongruent_598 (coe v0))
-- Function.Structures.IsBiEquivalence._.isEquivalence₂
d_isEquivalence'8322'_608 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_608 v0
  = coe
      d_isEquivalence'8322'_36 (coe d_to'45'isCongruent_598 (coe v0))
-- Function.Structures.IsBiEquivalence._.cong
d_cong_610 ::
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_610 v0
  = coe d_cong_32 (coe d_to'45'isCongruent_598 (coe v0))
-- Function.Structures.IsBiEquivalence._.Eq₁._≈_
d__'8776'__614 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> ()
d__'8776'__614 = erased
-- Function.Structures.IsBiEquivalence._.Eq₁._≉_
d__'8777'__616 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> ()
d__'8777'__616 = erased
-- Function.Structures.IsBiEquivalence._.Eq₁.Carrier
d_Carrier_618 ::
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
  (AgdaAny -> AgdaAny) -> T_IsBiEquivalence_584 -> ()
d_Carrier_618 = erased
-- Function.Structures.IsBiEquivalence._.Eq₁.isEquivalence
d_isEquivalence_620 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_isEquivalence_620 v11
du_isEquivalence_620 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_620 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe (coe d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.IsBiEquivalence._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_622 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_622 v11
du_isPartialEquivalence_622 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_622 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiEquivalence._.Eq₁.partialSetoid
d_partialSetoid_624 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_partialSetoid_624 v11
du_partialSetoid_624 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_624 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_40 (coe v1)))
-- Function.Structures.IsBiEquivalence._.Eq₁.refl
d_refl_626 ::
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
  (AgdaAny -> AgdaAny) -> T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny
d_refl_626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_626 v11
du_refl_626 :: T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny
du_refl_626 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8321'_34 (coe v1)))
-- Function.Structures.IsBiEquivalence._.Eq₁.reflexive
d_reflexive_628 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_628 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_628 v11
du_reflexive_628 ::
  T_IsBiEquivalence_584 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_628 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsBiEquivalence._.Eq₁.setoid
d_setoid_630 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_setoid_630 v11
du_setoid_630 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_630 v0
  = coe du_setoid_40 (coe d_to'45'isCongruent_598 (coe v0))
-- Function.Structures.IsBiEquivalence._.Eq₁.sym
d_sym_632 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_sym_632 v11
du_sym_632 ::
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_632 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiEquivalence._.Eq₁.trans
d_trans_634 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_trans_634 v11
du_trans_634 ::
  T_IsBiEquivalence_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_634 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiEquivalence._.Eq₂._≈_
d__'8776'__638 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> ()
d__'8776'__638 = erased
-- Function.Structures.IsBiEquivalence._.Eq₂._≉_
d__'8777'__640 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> ()
d__'8777'__640 = erased
-- Function.Structures.IsBiEquivalence._.Eq₂.Carrier
d_Carrier_642 ::
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
  (AgdaAny -> AgdaAny) -> T_IsBiEquivalence_584 -> ()
d_Carrier_642 = erased
-- Function.Structures.IsBiEquivalence._.Eq₂.isEquivalence
d_isEquivalence_644 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_isEquivalence_644 v11
du_isEquivalence_644 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_644 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe (coe d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.IsBiEquivalence._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_646 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_646 v11
du_isPartialEquivalence_646 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_646 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiEquivalence._.Eq₂.partialSetoid
d_partialSetoid_648 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_partialSetoid_648 v11
du_partialSetoid_648 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_648 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_66 (coe v1)))
-- Function.Structures.IsBiEquivalence._.Eq₂.refl
d_refl_650 ::
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
  (AgdaAny -> AgdaAny) -> T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny
d_refl_650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_650 v11
du_refl_650 :: T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny
du_refl_650 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8322'_36 (coe v1)))
-- Function.Structures.IsBiEquivalence._.Eq₂.reflexive
d_reflexive_652 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_652 v11
du_reflexive_652 ::
  T_IsBiEquivalence_584 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_652 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsBiEquivalence._.Eq₂.setoid
d_setoid_654 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_654 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_setoid_654 v11
du_setoid_654 ::
  T_IsBiEquivalence_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_654 v0
  = coe du_setoid_66 (coe d_to'45'isCongruent_598 (coe v0))
-- Function.Structures.IsBiEquivalence._.Eq₂.sym
d_sym_656 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_sym_656 v11
du_sym_656 ::
  T_IsBiEquivalence_584 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_656 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiEquivalence._.Eq₂.trans
d_trans_658 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiEquivalence_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_658 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_trans_658 v11
du_trans_658 ::
  T_IsBiEquivalence_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_658 v0
  = let v1 = d_to'45'isCongruent_598 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiInverse
d_IsBiInverse_666 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_IsBiInverse_666
  = C_IsBiInverse'46'constructor_32731 T_IsCongruent_22
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Structures.IsBiInverse.to-isCongruent
d_to'45'isCongruent_684 :: T_IsBiInverse_666 -> T_IsCongruent_22
d_to'45'isCongruent_684 v0
  = case coe v0 of
      C_IsBiInverse'46'constructor_32731 v1 v2 v3 v4 v5 -> coe v1
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBiInverse.from₁-cong
d_from'8321''45'cong_686 ::
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8321''45'cong_686 v0
  = case coe v0 of
      C_IsBiInverse'46'constructor_32731 v1 v2 v3 v4 v5 -> coe v2
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBiInverse.from₂-cong
d_from'8322''45'cong_688 ::
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'8322''45'cong_688 v0
  = case coe v0 of
      C_IsBiInverse'46'constructor_32731 v1 v2 v3 v4 v5 -> coe v3
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBiInverse.inverseˡ
d_inverse'737'_690 ::
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_690 v0
  = case coe v0 of
      C_IsBiInverse'46'constructor_32731 v1 v2 v3 v4 v5 -> coe v4
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBiInverse.inverseʳ
d_inverse'691'_692 ::
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_692 v0
  = case coe v0 of
      C_IsBiInverse'46'constructor_32731 v1 v2 v3 v4 v5 -> coe v5
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsBiInverse._.isEquivalence₁
d_isEquivalence'8321'_696 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_696 v0
  = coe
      d_isEquivalence'8321'_34 (coe d_to'45'isCongruent_684 (coe v0))
-- Function.Structures.IsBiInverse._.isEquivalence₂
d_isEquivalence'8322'_698 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_698 v0
  = coe
      d_isEquivalence'8322'_36 (coe d_to'45'isCongruent_684 (coe v0))
-- Function.Structures.IsBiInverse._.cong
d_cong_700 ::
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_700 v0
  = coe d_cong_32 (coe d_to'45'isCongruent_684 (coe v0))
-- Function.Structures.IsBiInverse._.Eq₁._≈_
d__'8776'__704 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> ()
d__'8776'__704 = erased
-- Function.Structures.IsBiInverse._.Eq₁._≉_
d__'8777'__706 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> ()
d__'8777'__706 = erased
-- Function.Structures.IsBiInverse._.Eq₁.Carrier
d_Carrier_708 ::
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
  (AgdaAny -> AgdaAny) -> T_IsBiInverse_666 -> ()
d_Carrier_708 = erased
-- Function.Structures.IsBiInverse._.Eq₁.isEquivalence
d_isEquivalence_710 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_isEquivalence_710 v11
du_isEquivalence_710 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_710 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe (coe d_isEquivalence'8321'_34 (coe v1))
-- Function.Structures.IsBiInverse._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_712 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_712 v11
du_isPartialEquivalence_712 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_712 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiInverse._.Eq₁.partialSetoid
d_partialSetoid_714 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_partialSetoid_714 v11
du_partialSetoid_714 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_714 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_40 (coe v1)))
-- Function.Structures.IsBiInverse._.Eq₁.refl
d_refl_716 ::
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
  (AgdaAny -> AgdaAny) -> T_IsBiInverse_666 -> AgdaAny -> AgdaAny
d_refl_716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_716 v11
du_refl_716 :: T_IsBiInverse_666 -> AgdaAny -> AgdaAny
du_refl_716 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8321'_34 (coe v1)))
-- Function.Structures.IsBiInverse._.Eq₁.reflexive
d_reflexive_718 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_718 v11
du_reflexive_718 ::
  T_IsBiInverse_666 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_718 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsBiInverse._.Eq₁.setoid
d_setoid_720 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_720 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_setoid_720 v11
du_setoid_720 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_720 v0
  = coe du_setoid_40 (coe d_to'45'isCongruent_684 (coe v0))
-- Function.Structures.IsBiInverse._.Eq₁.sym
d_sym_722 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_sym_722 v11
du_sym_722 ::
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_722 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiInverse._.Eq₁.trans
d_trans_724 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_trans_724 v11
du_trans_724 ::
  T_IsBiInverse_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_724 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (let v2 = coe du_setoid_40 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiInverse._.Eq₂._≈_
d__'8776'__728 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> ()
d__'8776'__728 = erased
-- Function.Structures.IsBiInverse._.Eq₂._≉_
d__'8777'__730 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> ()
d__'8777'__730 = erased
-- Function.Structures.IsBiInverse._.Eq₂.Carrier
d_Carrier_732 ::
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
  (AgdaAny -> AgdaAny) -> T_IsBiInverse_666 -> ()
d_Carrier_732 = erased
-- Function.Structures.IsBiInverse._.Eq₂.isEquivalence
d_isEquivalence_734 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_isEquivalence_734 v11
du_isEquivalence_734 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_734 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe (coe d_isEquivalence'8322'_36 (coe v1))
-- Function.Structures.IsBiInverse._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_736 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_736 v11
du_isPartialEquivalence_736 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_736 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiInverse._.Eq₂.partialSetoid
d_partialSetoid_738 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_738 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_partialSetoid_738 v11
du_partialSetoid_738 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_738 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
         (coe du_setoid_66 (coe v1)))
-- Function.Structures.IsBiInverse._.Eq₂.refl
d_refl_740 ::
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
  (AgdaAny -> AgdaAny) -> T_IsBiInverse_666 -> AgdaAny -> AgdaAny
d_refl_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_740 v11
du_refl_740 :: T_IsBiInverse_666 -> AgdaAny -> AgdaAny
du_refl_740 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe d_isEquivalence'8322'_36 (coe v1)))
-- Function.Structures.IsBiInverse._.Eq₂.reflexive
d_reflexive_742 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_742 v11
du_reflexive_742 ::
  T_IsBiInverse_666 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_742 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))
              v3))
-- Function.Structures.IsBiInverse._.Eq₂.setoid
d_setoid_744 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_setoid_744 v11
du_setoid_744 ::
  T_IsBiInverse_666 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_744 v0
  = coe du_setoid_66 (coe d_to'45'isCongruent_684 (coe v0))
-- Function.Structures.IsBiInverse._.Eq₂.sym
d_sym_746 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_746 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_sym_746 v11
du_sym_746 ::
  T_IsBiInverse_666 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_746 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsBiInverse._.Eq₂.trans
d_trans_748 ::
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
  (AgdaAny -> AgdaAny) ->
  T_IsBiInverse_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_748 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_trans_748 v11
du_trans_748 ::
  T_IsBiInverse_666 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_748 v0
  = let v1 = d_to'45'isCongruent_684 (coe v0) in
    coe
      (let v2 = coe du_setoid_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v2))))
-- Function.Structures.IsSplitSurjection
d_IsSplitSurjection_752 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsSplitSurjection_752
  = C_IsSplitSurjection'46'constructor_35501 (AgdaAny -> AgdaAny)
                                             T_IsLeftInverse_322
-- Function.Structures.IsSplitSurjection.from
d_from_760 :: T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny
d_from_760 v0
  = case coe v0 of
      C_IsSplitSurjection'46'constructor_35501 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsSplitSurjection.isLeftInverse
d_isLeftInverse_762 ::
  T_IsSplitSurjection_752 -> T_IsLeftInverse_322
d_isLeftInverse_762 v0
  = case coe v0 of
      C_IsSplitSurjection'46'constructor_35501 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Function.Structures.IsSplitSurjection._.from-cong
d_from'45'cong_766 ::
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_from'45'cong_766 v0
  = coe d_from'45'cong_336 (coe d_isLeftInverse_762 (coe v0))
-- Function.Structures.IsSplitSurjection._.inverseˡ
d_inverse'737'_768 ::
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_768 v0
  = coe d_inverse'737'_338 (coe d_isLeftInverse_762 (coe v0))
-- Function.Structures.IsSplitSurjection._.isCongruent
d_isCongruent_770 :: T_IsSplitSurjection_752 -> T_IsCongruent_22
d_isCongruent_770 v0
  = coe d_isCongruent_334 (coe d_isLeftInverse_762 (coe v0))
-- Function.Structures.IsSplitSurjection._.isEquivalence₁
d_isEquivalence'8321'_772 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8321'_772 v0
  = coe
      d_isEquivalence'8321'_34
      (coe d_isCongruent_334 (coe d_isLeftInverse_762 (coe v0)))
-- Function.Structures.IsSplitSurjection._.isEquivalence₂
d_isEquivalence'8322'_774 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence'8322'_774 v0
  = coe
      d_isEquivalence'8322'_36
      (coe d_isCongruent_334 (coe d_isLeftInverse_762 (coe v0)))
-- Function.Structures.IsSplitSurjection._.isSurjection
d_isSurjection_776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> T_IsSurjection_162
d_isSurjection_776 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isSurjection_776 v9
du_isSurjection_776 ::
  T_IsSplitSurjection_752 -> T_IsSurjection_162
du_isSurjection_776 v0
  = coe
      du_isSurjection_400 (coe d_from_760 (coe v0))
      (coe d_isLeftInverse_762 (coe v0))
-- Function.Structures.IsSplitSurjection._.strictlyInverseˡ
d_strictlyInverse'737'_778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny
d_strictlyInverse'737'_778 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_strictlyInverse'737'_778 v9
du_strictlyInverse'737'_778 ::
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny
du_strictlyInverse'737'_778 v0
  = coe
      du_strictlyInverse'737'_396 (coe d_from_760 (coe v0))
      (coe d_isLeftInverse_762 (coe v0))
-- Function.Structures.IsSplitSurjection._.cong
d_cong_780 ::
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_780 v0
  = coe
      d_cong_32
      (coe d_isCongruent_334 (coe d_isLeftInverse_762 (coe v0)))
-- Function.Structures.IsSplitSurjection._.Eq₁._≈_
d__'8776'__784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> ()
d__'8776'__784 = erased
-- Function.Structures.IsSplitSurjection._.Eq₁._≉_
d__'8777'__786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> ()
d__'8777'__786 = erased
-- Function.Structures.IsSplitSurjection._.Eq₁.Carrier
d_Carrier_788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsSplitSurjection_752 -> ()
d_Carrier_788 = erased
-- Function.Structures.IsSplitSurjection._.Eq₁.isEquivalence
d_isEquivalence_790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_790 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_790 v9
du_isEquivalence_790 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_790 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe (coe d_isEquivalence'8321'_34 (coe v2)))
-- Function.Structures.IsSplitSurjection._.Eq₁.isPartialEquivalence
d_isPartialEquivalence_792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_792 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_792 v9
du_isPartialEquivalence_792 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_792 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsSplitSurjection._.Eq₁.partialSetoid
d_partialSetoid_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_794 v9
du_partialSetoid_794 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_794 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe du_setoid_40 (coe v2))))
-- Function.Structures.IsSplitSurjection._.Eq₁.refl
d_refl_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny
d_refl_796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_796 v9
du_refl_796 :: T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny
du_refl_796 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe d_isEquivalence'8321'_34 (coe v2))))
-- Function.Structures.IsSplitSurjection._.Eq₁.reflexive
d_reflexive_798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_798 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_798 v9
du_reflexive_798 ::
  T_IsSplitSurjection_752 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_798 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Structures.IsSplitSurjection._.Eq₁.setoid
d_setoid_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_800 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_800 v9
du_setoid_800 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_800 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe (coe du_setoid_40 (coe d_isCongruent_334 (coe v1)))
-- Function.Structures.IsSplitSurjection._.Eq₁.sym
d_sym_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_802 v9
du_sym_802 ::
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_802 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsSplitSurjection._.Eq₁.trans
d_trans_804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_804 v9
du_trans_804 ::
  T_IsSplitSurjection_752 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_804 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_40 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsSplitSurjection._.Eq₂._≈_
d__'8776'__808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> ()
d__'8776'__808 = erased
-- Function.Structures.IsSplitSurjection._.Eq₂._≉_
d__'8777'__810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> ()
d__'8777'__810 = erased
-- Function.Structures.IsSplitSurjection._.Eq₂.Carrier
d_Carrier_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> T_IsSplitSurjection_752 -> ()
d_Carrier_812 = erased
-- Function.Structures.IsSplitSurjection._.Eq₂.isEquivalence
d_isEquivalence_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isEquivalence_814 v9
du_isEquivalence_814 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_814 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe (coe d_isEquivalence'8322'_36 (coe v2)))
-- Function.Structures.IsSplitSurjection._.Eq₂.isPartialEquivalence
d_isPartialEquivalence_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_816 v9
du_isPartialEquivalence_816 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_816 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsSplitSurjection._.Eq₂.partialSetoid
d_partialSetoid_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_partialSetoid_818 v9
du_partialSetoid_818 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_818 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70
            (coe du_setoid_66 (coe v2))))
-- Function.Structures.IsSplitSurjection._.Eq₂.refl
d_refl_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny
d_refl_820 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_refl_820 v9
du_refl_820 :: T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny
du_refl_820 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe d_isEquivalence'8322'_36 (coe v2))))
-- Function.Structures.IsSplitSurjection._.Eq₂.reflexive
d_reflexive_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_822 v9
du_reflexive_822 ::
  T_IsSplitSurjection_752 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_822 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v3))
                 v4)))
-- Function.Structures.IsSplitSurjection._.Eq₂.setoid
d_setoid_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_824 v9
du_setoid_824 ::
  T_IsSplitSurjection_752 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_824 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe (coe du_setoid_66 (coe d_isCongruent_334 (coe v1)))
-- Function.Structures.IsSplitSurjection._.Eq₂.sym
d_sym_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_sym_826 v9
du_sym_826 ::
  T_IsSplitSurjection_752 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_826 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
-- Function.Structures.IsSplitSurjection._.Eq₂.trans
d_trans_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  T_IsSplitSurjection_752 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_828 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_trans_828 v9
du_trans_828 ::
  T_IsSplitSurjection_752 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_828 v0
  = let v1 = d_isLeftInverse_762 (coe v0) in
    coe
      (let v2 = d_isCongruent_334 (coe v1) in
       coe
         (let v3 = coe du_setoid_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v3)))))
