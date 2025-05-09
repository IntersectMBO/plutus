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

module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles qualified
import MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Indexed.Heterogeneous.Construct.Trivial._.Aᵢ
d_A'7522'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> ()
d_A'7522'_24 = erased
-- Relation.Binary.Indexed.Heterogeneous.Construct.Trivial._.isIndexedEquivalence
d_isIndexedEquivalence_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
d_isIndexedEquivalence_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isIndexedEquivalence_32 v6
du_isIndexedEquivalence_32 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
du_isIndexedEquivalence_32 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.C_IsIndexedEquivalence'46'constructor_1089
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v0)))
      (coe
         (\ v1 v2 ->
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v0)))
      (coe
         (\ v1 v2 v3 ->
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Construct.Trivial._.isIndexedPreorder
d_isIndexedPreorder_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_44
d_isIndexedPreorder_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isIndexedPreorder_60 v8
du_isIndexedPreorder_60 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_44
du_isIndexedPreorder_60 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.C_IsIndexedPreorder'46'constructor_5837
      (coe
         du_isIndexedEquivalence_32
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe v0)))
      (coe
         (\ v1 v2 ->
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82 (coe v0)))
      (coe
         (\ v1 v2 v3 ->
            MAlonzo.Code.Relation.Binary.Structures.d_trans_84 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.indexedSetoid
d_indexedSetoid_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18
d_indexedSetoid_106 ~v0 ~v1 ~v2 ~v3 v4 = du_indexedSetoid_106 v4
du_indexedSetoid_106 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18
du_indexedSetoid_106 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.C_IndexedSetoid'46'constructor_445
      (coe
         du_isIndexedEquivalence_32
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.indexedPreorder
d_indexedPreorder_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedPreorder_60
d_indexedPreorder_142 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_indexedPreorder_142 v5
du_indexedPreorder_142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedPreorder_60
du_indexedPreorder_142 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.C_IndexedPreorder'46'constructor_1987
      (coe
         du_isIndexedPreorder_60
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0)))
