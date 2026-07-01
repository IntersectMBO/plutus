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

module MAlonzo.Code.IO.Primitive.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.IO
import qualified MAlonzo.Code.Agda.Primitive

-- IO.Primitive.Core.pure
d_pure_12 ::
  forall xA'46'a.
    forall xA.
      MAlonzo.Code.Agda.Primitive.T_Level_18 ->
      () -> xA -> MAlonzo.Code.Agda.Builtin.IO.T_IO_8 xA'46'a xA
d_pure_12 = \_ _ -> return
-- IO.Primitive.Core._>>=_
d__'62''62''61'__14 ::
  forall xA'46'a.
    forall xA.
      forall xB'46'a.
        forall xB.
          MAlonzo.Code.Agda.Primitive.T_Level_18 ->
          () ->
          MAlonzo.Code.Agda.Primitive.T_Level_18 ->
          () ->
          MAlonzo.Code.Agda.Builtin.IO.T_IO_8 xA'46'a xA ->
          (xA -> MAlonzo.Code.Agda.Builtin.IO.T_IO_8 xB'46'a xB) ->
          MAlonzo.Code.Agda.Builtin.IO.T_IO_8 xB'46'a xB
d__'62''62''61'__14 = \_ _ _ _ -> (>>=)
-- IO.Primitive.Core.return
d_return_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny
d_return_16 v0 ~v1 = du_return_16 v0
du_return_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny
du_return_16 v0 = coe d_pure_12 v0 erased
-- IO.Primitive.Core._>>_
d__'62''62'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny
d__'62''62'__18 v0 ~v1 v2 ~v3 v4 v5 = du__'62''62'__18 v0 v2 v4 v5
du__'62''62'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny
du__'62''62'__18 v0 v1 v2 v3
  = coe d__'62''62''61'__14 v0 erased v1 erased v2 (\ v4 -> v3)
