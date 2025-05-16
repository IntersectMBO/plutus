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

module MAlonzo.Code.Data.Irrelevant where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Irrelevant.Irrelevant
d_Irrelevant_20 a0 a1 = ()
data T_Irrelevant_20 = C_'91'_'93'_28
-- Data.Irrelevant.map
d_map_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> T_Irrelevant_20 -> T_Irrelevant_20
d_map_30 = erased
-- Data.Irrelevant.pure
d_pure_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> T_Irrelevant_20
d_pure_36 = erased
-- Data.Irrelevant._<*>_
d__'60''42''62'__40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Irrelevant_20 -> T_Irrelevant_20 -> T_Irrelevant_20
d__'60''42''62'__40 = erased
-- Data.Irrelevant._>>=_
d__'62''62''61'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Irrelevant_20 -> (AgdaAny -> T_Irrelevant_20) -> T_Irrelevant_20
d__'62''62''61'__46 = erased
-- Data.Irrelevant.zipWith
d_zipWith_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Irrelevant_20 -> T_Irrelevant_20 -> T_Irrelevant_20
d_zipWith_52 = erased
