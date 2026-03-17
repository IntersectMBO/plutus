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

module MAlonzo.Code.Data.Maybe.Relation.Binary.Pointwise where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Maybe.Relation.Binary.Pointwise.Pointwise
d_Pointwise_22 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Pointwise_22 = C_just_40 AgdaAny | C_nothing_42
-- Data.Maybe.Relation.Binary.Pointwise._.drop-just
d_drop'45'just_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Pointwise_22 -> AgdaAny
d_drop'45'just_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_drop'45'just_64 v8
du_drop'45'just_64 :: T_Pointwise_22 -> AgdaAny
du_drop'45'just_64 v0
  = case coe v0 of
      C_just_40 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Pointwise._.just-equivalence
d_just'45'equivalence_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_just'45'equivalence_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_just'45'equivalence_72
du_just'45'equivalence_72 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_just'45'equivalence_72
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2414 (coe C_just_40)
      (coe du_drop'45'just_64)
-- Data.Maybe.Relation.Binary.Pointwise._.nothing-inv
d_nothing'45'inv_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe AgdaAny ->
  T_Pointwise_22 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nothing'45'inv_76 = erased
-- Data.Maybe.Relation.Binary.Pointwise._.just-inv
d_just'45'inv_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  Maybe AgdaAny ->
  T_Pointwise_22 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_just'45'inv_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_just'45'inv_84 v7 v8
du_just'45'inv_84 ::
  Maybe AgdaAny ->
  T_Pointwise_22 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_just'45'inv_84 v0 v1
  = case coe v1 of
      C_just_40 v4
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_'45''44'__92 (coe v5)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Pointwise._.refl
d_refl_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> T_Pointwise_22
d_refl_100 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_refl_100 v4 v5
du_refl_100 ::
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> T_Pointwise_22
du_refl_100 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe C_just_40 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_nothing_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Pointwise._.reflexive
d_reflexive_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Pointwise_22
d_reflexive_106 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_reflexive_106 v4 v5
du_reflexive_106 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Maybe AgdaAny -> T_Pointwise_22
du_reflexive_106 v0 v1
  = coe du_refl_100 (coe (\ v2 -> coe v0 v2 v2 erased)) (coe v1)
-- Data.Maybe.Relation.Binary.Pointwise._.sym
d_sym_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> T_Pointwise_22 -> T_Pointwise_22
d_sym_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_sym_130 v8 v9 v10 v11
du_sym_130 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> T_Pointwise_22 -> T_Pointwise_22
du_sym_130 v0 v1 v2 v3
  = case coe v3 of
      C_just_40 v6
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                      -> coe C_just_40 (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nothing_42 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Pointwise._.trans
d_trans_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> T_Pointwise_22 -> T_Pointwise_22 -> T_Pointwise_22
d_trans_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
            v13 v14 v15 v16 v17
  = du_trans_166 v12 v13 v14 v15 v16 v17
du_trans_166 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> T_Pointwise_22 -> T_Pointwise_22 -> T_Pointwise_22
du_trans_166 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_just_40 v8
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_just_40 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_just_40 (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nothing_42 -> coe seq (coe v5) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Pointwise._.dec
d_dec_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_dec_188 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_dec_188 v4 v5 v6
du_dec_188 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_dec_188 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
                    (coe du_just'45'equivalence_72) (coe v0 v3 v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe C_nothing_42))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Pointwise._.isEquivalence
d_isEquivalence_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_206 ~v0 ~v1 ~v2 ~v3 v4 = du_isEquivalence_206 v4
du_isEquivalence_206 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_206 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         du_refl_100
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v0)))
      (coe
         du_sym_130
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v0)))
      (coe
         du_trans_166
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v0)))
-- Data.Maybe.Relation.Binary.Pointwise._.isDecEquivalence
d_isDecEquivalence_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_226 ~v0 ~v1 ~v2 ~v3 v4
  = du_isDecEquivalence_226 v4
du_isDecEquivalence_226 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_226 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe
         du_isEquivalence_206
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe v0)))
      (coe
         du_dec_188
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52 (coe v0)))
-- Data.Maybe.Relation.Binary.Pointwise._.pointwise⊆any
d_pointwise'8838'any_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  Maybe AgdaAny ->
  T_Pointwise_22 ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.Any.T_Any_18
d_pointwise'8838'any_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_pointwise'8838'any_252 v6
du_pointwise'8838'any_252 ::
  T_Pointwise_22 ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.Any.T_Any_18
du_pointwise'8838'any_252 v0
  = case coe v0 of
      C_just_40 v3
        -> coe MAlonzo.Code.Data.Maybe.Relation.Unary.Any.C_just_30 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Binary.Pointwise._.setoid
d_setoid_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_264 ~v0 ~v1 v2 = du_setoid_264 v2
du_setoid_264 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_264 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
      (coe
         du_isEquivalence_206
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
-- Data.Maybe.Relation.Binary.Pointwise._.decSetoid
d_decSetoid_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86
d_decSetoid_296 ~v0 ~v1 v2 = du_decSetoid_296 v2
du_decSetoid_296 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86
du_decSetoid_296 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1435
      (coe
         du_isDecEquivalence_226
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_102
            (coe v0)))
