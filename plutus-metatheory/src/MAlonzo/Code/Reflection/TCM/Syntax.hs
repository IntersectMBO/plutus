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

module MAlonzo.Code.Reflection.TCM.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Primitive

-- Reflection.TCM.Syntax._<|>_
d__'60''124''62'__14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__14 v0 ~v1 = du__'60''124''62'__14 v0
du__'60''124''62'__14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'60''124''62'__14 v0
  = coe MAlonzo.Code.Agda.Builtin.Reflection.d_catchTC_358 v0 erased
-- Reflection.TCM.Syntax._>>=_
d__'62''62''61'__16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__16 v0 ~v1 v2 ~v3 = du__'62''62''61'__16 v0 v2
du__'62''62''61'__16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'62''62''61'__16 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 v0 v1 erased
      erased
-- Reflection.TCM.Syntax._>>_
d__'62''62'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__18 v0 ~v1 v2 ~v3 v4 v5 = du__'62''62'__18 v0 v2 v4 v5
du__'62''62'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 v0 v1 erased
      erased v2 (\ v4 -> v3)
-- Reflection.TCM.Syntax._<*>_
d__'60''42''62'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__26 v0 ~v1 v2 ~v3 v4 v5
  = du__'60''42''62'__26 v0 v2 v4 v5
du__'60''42''62'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''62'__26 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () v1 erased
      erased v2
      (\ v4 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 v0 v1 erased
           erased v3
           (\ v5 ->
              coe
                MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 v1 erased
                (coe v4 v5)))
-- Reflection.TCM.Syntax._<$>_
d__'60''36''62'__36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__36 v0 ~v1 v2 ~v3 v4 v5
  = du__'60''36''62'__36 v0 v2 v4 v5
du__'60''36''62'__36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 v0 v1 erased
      erased v3
      (\ v4 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 v1 erased
           (coe v2 v4))
-- Reflection.TCM.Syntax._<$_
d__'60''36'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__44 v0 ~v1 v2 ~v3 v4 v5 = du__'60''36'__44 v0 v2 v4 v5
du__'60''36'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__44 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 v1 v0 erased
      erased v3
      (\ v4 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 v0 erased v2)
-- Reflection.TCM.Syntax._<&>_
d__'60''38''62'__52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__52 v0 ~v1 v2 ~v3 v4 v5
  = du__'60''38''62'__52 v0 v2 v4 v5
du__'60''38''62'__52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__52 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 v0 v1 erased
      erased v2
      (\ v4 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 v1 erased
           (coe v3 v4))
