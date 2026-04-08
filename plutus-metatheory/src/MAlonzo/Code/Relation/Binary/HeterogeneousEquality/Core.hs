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

module MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- Relation.Binary.HeterogeneousEquality.Core._≅_
d__'8773'__22 a0 a1 a2 a3 a4 a5 = ()
data T__'8773'__22 = C_refl_28
-- Relation.Binary.HeterogeneousEquality.Core.≅-to-≡
d_'8773''45'to'45''8801'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T__'8773'__22 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'to'45''8801'_34 = erased
-- Relation.Binary.HeterogeneousEquality.Core.≡-to-≅
d_'8801''45'to'45''8773'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8773'__22
d_'8801''45'to'45''8773'_40 = erased
