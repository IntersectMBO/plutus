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

module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedSetoid
d_IndexedSetoid_18 a0 a1 a2 a3 = ()
newtype T_IndexedSetoid_18
  = C_IndexedSetoid'46'constructor_445 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
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
      C_IndexedSetoid'46'constructor_445 v3 -> coe v3
      _                                     -> MAlonzo.RTE.mazUnreachableError
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
d_IndexedPreorder_60 a0 a1 a2 a3 a4 = ()
newtype T_IndexedPreorder_60
  = C_IndexedPreorder'46'constructor_1987 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_44
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder.Carrier
d_Carrier_80 :: T_IndexedPreorder_60 -> AgdaAny -> ()
d_Carrier_80 = erased
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._≈_
d__'8776'__82 ::
  T_IndexedPreorder_60 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8776'__82 = erased
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._≲_
d__'8818'__84 ::
  T_IndexedPreorder_60 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8818'__84 = erased
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder.isPreorder
d_isPreorder_86 ::
  T_IndexedPreorder_60 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_44
d_isPreorder_86 v0
  = case coe v0 of
      C_IndexedPreorder'46'constructor_1987 v4 -> coe v4
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.isEquivalence
d_isEquivalence_90 ::
  T_IndexedPreorder_60 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22
d_isEquivalence_90 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_60
      (coe d_isPreorder_86 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.refl
d_refl_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IndexedPreorder_60 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_92 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_92 v5
du_refl_92 :: T_IndexedPreorder_60 -> AgdaAny -> AgdaAny -> AgdaAny
du_refl_92 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.du_refl_80
      (coe d_isPreorder_86 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.reflexive
d_reflexive_94 ::
  T_IndexedPreorder_60 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_94 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_reflexive_66
      (coe d_isPreorder_86 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.trans
d_trans_96 ::
  T_IndexedPreorder_60 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_96 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_trans_68
      (coe d_isPreorder_86 (coe v0))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.Eq.refl
d_refl_100 :: T_IndexedPreorder_60 -> AgdaAny -> AgdaAny -> AgdaAny
d_refl_100 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_refl_30
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_60
         (coe d_isPreorder_86 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.Eq.reflexive
d_reflexive_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IndexedPreorder_60 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_102 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_102 v5
du_reflexive_102 ::
  T_IndexedPreorder_60 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_102 v0
  = let v1 = d_isPreorder_86 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.du_reflexive_38
           (coe
              MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_60
              (coe v1))
           v2 v3)
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.Eq.sym
d_sym_104 ::
  T_IndexedPreorder_60 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_104 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_sym_32
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_60
         (coe d_isPreorder_86 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._.Eq.trans
d_trans_106 ::
  T_IndexedPreorder_60 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_106 v0
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_trans_34
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_60
         (coe d_isPreorder_86 (coe v0)))
-- Relation.Binary.Indexed.Heterogeneous.Bundles.IndexedPreorder._∼_
d__'8764'__108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IndexedPreorder_60 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d__'8764'__108 = erased
