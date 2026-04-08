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

module MAlonzo.Code.Function.Indexed.Relation.Binary.Equality where

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

-- Function.Indexed.Relation.Binary.Equality.≡-setoid
d_'8801''45'setoid_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_18 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8801''45'setoid_18 v4
du_'8801''45'setoid_18 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_'8801''45'setoid_18 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_refl_30
                 (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.d_isEquivalence_38
                    (coe v0))
                 v2 (coe v1 v2)))
         (coe
            (\ v1 v2 v3 v4 ->
               coe
                 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_sym_32
                 (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.d_isEquivalence_38
                    (coe v0))
                 v4 v4 (coe v1 v4) (coe v2 v4) (coe v3 v4)))
         (coe
            (\ v1 v2 v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_trans_34
                 (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.d_isEquivalence_38
                    (coe v0))
                 v6 v6 v6 (coe v1 v6) (coe v2 v6) (coe v3 v6) (coe v4 v6)
                 (coe v5 v6))))
