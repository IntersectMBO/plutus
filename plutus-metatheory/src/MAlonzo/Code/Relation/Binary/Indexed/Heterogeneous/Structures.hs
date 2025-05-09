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

module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedEquivalence
d_IsIndexedEquivalence_22 a0 a1 a2 a3 a4 a5 = ()
data T_IsIndexedEquivalence_22
  = C_IsIndexedEquivalence'46'constructor_1089 (AgdaAny ->
                                                AgdaAny -> AgdaAny)
                                               (AgdaAny ->
                                                AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                               (AgdaAny ->
                                                AgdaAny ->
                                                AgdaAny ->
                                                AgdaAny ->
                                                AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedEquivalence.refl
d_refl_30 ::
  T_IsIndexedEquivalence_22 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_30 v0
  = case coe v0 of
      C_IsIndexedEquivalence'46'constructor_1089 v1 v2 v3 -> coe v1
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedEquivalence.sym
d_sym_32 ::
  T_IsIndexedEquivalence_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_32 v0
  = case coe v0 of
      C_IsIndexedEquivalence'46'constructor_1089 v1 v2 v3 -> coe v2
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedEquivalence.trans
d_trans_34 ::
  T_IsIndexedEquivalence_22 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_34 v0
  = case coe v0 of
      C_IsIndexedEquivalence'46'constructor_1089 v1 v2 v3 -> coe v3
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedEquivalence.reflexive
d_reflexive_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T_IsIndexedEquivalence_22 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 ~v10
  = du_reflexive_38 v6 v7 v8
du_reflexive_38 ::
  T_IsIndexedEquivalence_22 -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_38 v0 v1 v2 = coe d_refl_30 v0 v1 v2
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder
d_IsIndexedPreorder_44 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsIndexedPreorder_44
  = C_IsIndexedPreorder'46'constructor_5837 T_IsIndexedEquivalence_22
                                            (AgdaAny ->
                                             AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                            (AgdaAny ->
                                             AgdaAny ->
                                             AgdaAny ->
                                             AgdaAny ->
                                             AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder.isEquivalence
d_isEquivalence_60 ::
  T_IsIndexedPreorder_44 -> T_IsIndexedEquivalence_22
d_isEquivalence_60 v0
  = case coe v0 of
      C_IsIndexedPreorder'46'constructor_5837 v1 v2 v3 -> coe v1
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder.reflexive
d_reflexive_66 ::
  T_IsIndexedPreorder_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_66 v0
  = case coe v0 of
      C_IsIndexedPreorder'46'constructor_5837 v1 v2 v3 -> coe v2
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder.trans
d_trans_68 ::
  T_IsIndexedPreorder_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_68 v0
  = case coe v0 of
      C_IsIndexedPreorder'46'constructor_5837 v1 v2 v3 -> coe v3
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder.Eq.refl
d_refl_72 ::
  T_IsIndexedPreorder_44 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_72 v0 = coe d_refl_30 (coe d_isEquivalence_60 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder.Eq.reflexive
d_reflexive_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T_IsIndexedPreorder_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_74 v8
du_reflexive_74 ::
  T_IsIndexedPreorder_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_74 v0 v1 v2 v3 v4
  = coe du_reflexive_38 (coe d_isEquivalence_60 (coe v0)) v1 v2
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder.Eq.sym
d_sym_76 ::
  T_IsIndexedPreorder_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_76 v0 = coe d_sym_32 (coe d_isEquivalence_60 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder.Eq.trans
d_trans_78 ::
  T_IsIndexedPreorder_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_78 v0 = coe d_trans_34 (coe d_isEquivalence_60 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Structures.IsIndexedPreorder.refl
d_refl_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T_IsIndexedPreorder_44 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_80 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_refl_80 v8 v9 v10
du_refl_80 ::
  T_IsIndexedPreorder_44 -> AgdaAny -> AgdaAny -> AgdaAny
du_refl_80 v0 v1 v2
  = coe
      d_reflexive_66 v0 v1 v1 v2 v2
      (coe d_refl_30 (d_isEquivalence_60 (coe v0)) v1 v2)
