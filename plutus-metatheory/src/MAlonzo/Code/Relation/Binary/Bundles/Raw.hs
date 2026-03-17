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

module MAlonzo.Code.Relation.Binary.Bundles.Raw where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Relation.Binary.Bundles.Raw.RawSetoid
d_RawSetoid_12 a0 a1 = ()
data T_RawSetoid_12 = C_RawSetoid'46'constructor_45
-- Relation.Binary.Bundles.Raw.RawSetoid.Carrier
d_Carrier_22 :: T_RawSetoid_12 -> ()
d_Carrier_22 = erased
-- Relation.Binary.Bundles.Raw.RawSetoid._≈_
d__'8776'__24 :: T_RawSetoid_12 -> AgdaAny -> AgdaAny -> ()
d__'8776'__24 = erased
-- Relation.Binary.Bundles.Raw.RawSetoid._≉_
d__'8777'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawSetoid_12 -> AgdaAny -> AgdaAny -> ()
d__'8777'__26 = erased
-- Relation.Binary.Bundles.Raw.RawRelation
d_RawRelation_38 a0 a1 a2 = ()
data T_RawRelation_38 = C_RawRelation'46'constructor_439
-- Relation.Binary.Bundles.Raw.RawRelation.Carrier
d_Carrier_52 :: T_RawRelation_38 -> ()
d_Carrier_52 = erased
-- Relation.Binary.Bundles.Raw.RawRelation._≈_
d__'8776'__54 :: T_RawRelation_38 -> AgdaAny -> AgdaAny -> ()
d__'8776'__54 = erased
-- Relation.Binary.Bundles.Raw.RawRelation._∼_
d__'8764'__56 :: T_RawRelation_38 -> AgdaAny -> AgdaAny -> ()
d__'8764'__56 = erased
-- Relation.Binary.Bundles.Raw.RawRelation.rawSetoid
d_rawSetoid_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRelation_38 -> T_RawSetoid_12
d_rawSetoid_58 = erased
-- Relation.Binary.Bundles.Raw.RawRelation._._≉_
d__'8777'__62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRelation_38 -> AgdaAny -> AgdaAny -> ()
d__'8777'__62 = erased
-- Relation.Binary.Bundles.Raw.RawRelation._≁_
d__'8769'__64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRelation_38 -> AgdaAny -> AgdaAny -> ()
d__'8769'__64 = erased
-- Relation.Binary.Bundles.Raw.RawRelation._∼ᵒ_
d__'8764''7506'__70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRelation_38 -> AgdaAny -> AgdaAny -> ()
d__'8764''7506'__70 = erased
-- Relation.Binary.Bundles.Raw.RawRelation._≁ᵒ_
d__'8769''7506'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawRelation_38 -> AgdaAny -> AgdaAny -> ()
d__'8769''7506'__72 = erased
