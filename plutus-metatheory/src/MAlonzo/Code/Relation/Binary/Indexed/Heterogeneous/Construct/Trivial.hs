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

module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures
import qualified MAlonzo.Code.Relation.Binary.Structures

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
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
d_isIndexedEquivalence_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isIndexedEquivalence_32 v6
du_isIndexedEquivalence_32 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
du_isIndexedEquivalence_32 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.C_constructor_40
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36 (coe v0)))
      (coe
         (\ v1 v2 ->
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38 (coe v0)))
      (coe
         (\ v1 v2 v3 ->
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v0)))
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_46
d_isIndexedPreorder_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isIndexedPreorder_60 v8
du_isIndexedPreorder_60 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_46
du_isIndexedPreorder_60 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.C_constructor_84
      (coe
         du_isIndexedEquivalence_32
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v0)))
      (coe
         (\ v1 v2 ->
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 (coe v0)))
      (coe
         (\ v1 v2 v3 ->
            MAlonzo.Code.Relation.Binary.Structures.d_trans_90 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.indexedSetoid
d_indexedSetoid_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18
d_indexedSetoid_106 ~v0 ~v1 ~v2 ~v3 v4 = du_indexedSetoid_106 v4
du_indexedSetoid_106 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18
du_indexedSetoid_106 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.C_constructor_50
      (coe
         du_isIndexedEquivalence_32
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.indexedPreorder
d_indexedPreorder_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedPreorder_62
d_indexedPreorder_144 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_indexedPreorder_144 v5
du_indexedPreorder_144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedPreorder_62
du_indexedPreorder_144 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.C_constructor_112
      (coe
         du_isIndexedPreorder_60
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
