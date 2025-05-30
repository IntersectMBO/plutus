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

module MAlonzo.Code.Function.Dependent.Bundles where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Dependent.Bundles._._._≈_
d__'8776'__32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__32 = erased
-- Function.Dependent.Bundles._._.Carrier
d_Carrier_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  ()
d_Carrier_34 = erased
-- Function.Dependent.Bundles._.Func
d_Func_42 a0 a1 a2 a3 a4 a5 = ()
data T_Func_42
  = C_Func'46'constructor_677 (AgdaAny -> AgdaAny)
                              (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Dependent.Bundles._.Func.to
d_to_56 :: T_Func_42 -> AgdaAny -> AgdaAny
d_to_56 v0
  = case coe v0 of
      C_Func'46'constructor_677 v1 v2 -> coe v1
      _                               -> MAlonzo.RTE.mazUnreachableError
-- Function.Dependent.Bundles._.Func.cong
d_cong_62 :: T_Func_42 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_62 v0
  = case coe v0 of
      C_Func'46'constructor_677 v1 v2 -> coe v2
      _                               -> MAlonzo.RTE.mazUnreachableError
