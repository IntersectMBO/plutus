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

module MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
