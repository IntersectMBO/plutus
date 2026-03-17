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

module MAlonzo.Code.Class.Show.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive

-- Class.Show.Core.Show
d_Show_10 a0 a1 = ()
newtype T_Show_10
  = C_mkShow_18 (AgdaAny ->
                 MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Class.Show.Core.Show.show
d_show_16 ::
  T_Show_10 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show_16 v0
  = case coe v0 of
      C_mkShow_18 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Show.Core._.show
d_show_22 ::
  T_Show_10 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show_22 v0 = coe d_show_16 (coe v0)
-- Class.Show.Core.Show¹
d_Show'185'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> (AgdaAny -> ()) -> ()
d_Show'185'_24 = erased
-- Class.Show.Core.Show²
d_Show'178'_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> ()
d_Show'178'_26 = erased
-- Class.Show.Core.Show³
d_Show'179'_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) -> ()
d_Show'179'_28 = erased
