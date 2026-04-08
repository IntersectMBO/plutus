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

module MAlonzo.Code.Function.Dependent.Bundles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles

-- Function.Dependent.Bundles._._._≈_
d__'8776'__32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__32 = erased
-- Function.Dependent.Bundles._._.Carrier
d_Carrier_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  ()
d_Carrier_34 = erased
-- Function.Dependent.Bundles._.Func
d_Func_42 a0 a1 a2 a3 a4 a5 = ()
data T_Func_42
  = C_constructor_64 (AgdaAny -> AgdaAny)
                     (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Function.Dependent.Bundles._.Func.to
d_to_56 :: T_Func_42 -> AgdaAny -> AgdaAny
d_to_56 v0
  = case coe v0 of
      C_constructor_64 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Dependent.Bundles._.Func.cong
d_cong_62 :: T_Func_42 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_62 v0
  = case coe v0 of
      C_constructor_64 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
