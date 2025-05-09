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

module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.At where

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

-- Relation.Binary.Indexed.Heterogeneous.Construct.At._.isEquivalence
d_isEquivalence_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_30 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_isEquivalence_30 v6 v7
du_isEquivalence_30 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedEquivalence_22 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_30 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_refl_30
         v0 v1)
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_sym_32
         v0 v1 v1)
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_trans_34
         v0 v1 v1 v1)
-- Relation.Binary.Indexed.Heterogeneous.Construct.At._.isPreorder
d_isPreorder_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_44 ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_isPreorder_60 v8 v9
du_isPreorder_60 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.T_IsIndexedPreorder_44 ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_60 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         du_isEquivalence_30
         (coe
            MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_isEquivalence_60
            (coe v0))
         (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_reflexive_66
         v0 v1 v1)
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_trans_68
         v0 v1 v1 v1)
-- Relation.Binary.Indexed.Heterogeneous.Construct.At._.setoid
d_setoid_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_102 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_setoid_102 v4 v5
du_setoid_102 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_102 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (coe
         du_isEquivalence_30
         (coe
            MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.d_isEquivalence_38
            (coe v0))
         (coe v1))
-- Relation.Binary.Indexed.Heterogeneous.Construct.At._.preorder
d_preorder_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedPreorder_60 ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_132 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_preorder_132 v5 v6
du_preorder_132 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedPreorder_60 ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_132 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      (coe
         du_isPreorder_60
         (coe
            MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.d_isPreorder_86
            (coe v0))
         (coe v1))
-- Relation.Binary.Indexed.Heterogeneous.Construct.At._._atₛ_
d__at'8347'__184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d__at'8347'__184 ~v0 ~v1 ~v2 ~v3 = du__at'8347'__184
du__at'8347'__184 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du__at'8347'__184 = coe du_setoid_102
