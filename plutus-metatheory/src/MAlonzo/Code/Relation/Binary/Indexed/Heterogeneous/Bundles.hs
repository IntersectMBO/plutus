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

module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures

-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid
d_IndexedSetoid_18 a0 a1 a2 a3 = ()
newtype T_IndexedSetoid_18
  = C_constructor_50 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid.Carrier
d_Carrier_34 :: T_IndexedSetoid_18 -> AgdaAny -> ()
d_Carrier_34 = erased
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid._≈_
d__'8776'__36 ::
  T_IndexedSetoid_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8776'__36 = erased
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid.isEquivalence
d_isEquivalence_38 ::
  T_IndexedSetoid_18 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
d_isEquivalence_38 v0
  = case coe v0 of
      C_constructor_50 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid._.refl
d_refl_42 :: T_IndexedSetoid_18 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_42 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_refl_30
      (coe d_isEquivalence_38 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid._.reflexive
d_reflexive_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IndexedSetoid_18 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_44 ~v0 ~v1 ~v2 ~v3 v4 = du_reflexive_44 v4
du_reflexive_44 ::
  T_IndexedSetoid_18 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.du_reflexive_38
      (coe d_isEquivalence_38 (coe v0)) v1 v2
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid._.sym
d_sym_46 ::
  T_IndexedSetoid_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_46 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_sym_32
      (coe d_isEquivalence_38 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid._.trans
d_trans_48 ::
  T_IndexedSetoid_18 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_48 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_trans_34
      (coe d_isEquivalence_38 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder
d_IndexedPreorder_62 a0 a1 a2 a3 a4 = ()
newtype T_IndexedPreorder_62
  = C_constructor_112 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_46
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder.Carrier
d_Carrier_82 :: T_IndexedPreorder_62 -> AgdaAny -> ()
d_Carrier_82 = erased
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._≈_
d__'8776'__84 ::
  T_IndexedPreorder_62 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8776'__84 = erased
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._≲_
d__'8818'__86 ::
  T_IndexedPreorder_62 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8818'__86 = erased
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder.isPreorder
d_isPreorder_88 ::
  T_IndexedPreorder_62 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_46
d_isPreorder_88 v0
  = case coe v0 of
      C_constructor_112 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.isEquivalence
d_isEquivalence_92 ::
  T_IndexedPreorder_62 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
d_isEquivalence_92 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_62
      (coe d_isPreorder_88 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.refl
d_refl_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IndexedPreorder_62 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_94 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_94 v5
du_refl_94 :: T_IndexedPreorder_62 -> AgdaAny -> AgdaAny -> AgdaAny
du_refl_94 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.du_refl_82
      (coe d_isPreorder_88 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.reflexive
d_reflexive_96 ::
  T_IndexedPreorder_62 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_96 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_reflexive_68
      (coe d_isPreorder_88 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.trans
d_trans_98 ::
  T_IndexedPreorder_62 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_98 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_trans_70
      (coe d_isPreorder_88 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.Eq.refl
d_refl_102 :: T_IndexedPreorder_62 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_102 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_refl_30
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_62
         (coe d_isPreorder_88 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.Eq.reflexive
d_reflexive_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IndexedPreorder_62 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_104 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_104 v5
du_reflexive_104 ::
  T_IndexedPreorder_62 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_104 v0
  = let v1 = d_isPreorder_88 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.du_reflexive_38
           (coe
              MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_62
              (coe v1))
           v2 v3)
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.Eq.sym
d_sym_106 ::
  T_IndexedPreorder_62 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_106 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_sym_32
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_62
         (coe d_isPreorder_88 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.Eq.trans
d_trans_108 ::
  T_IndexedPreorder_62 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_108 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_trans_34
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_62
         (coe d_isPreorder_88 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._∼_
d__'8764'__110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IndexedPreorder_62 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8764'__110 = erased
