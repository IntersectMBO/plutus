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

module MAlonzo.Code.Effect.Choice where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Effect.Choice.RawChoice
d_RawChoice_16 a0 a1 a2 = ()
newtype T_RawChoice_16
  = C_RawChoice'46'constructor_149 (() ->
                                    AgdaAny -> AgdaAny -> AgdaAny)
-- Effect.Choice.RawChoice._<|>_
d__'60''124''62'__22 ::
  T_RawChoice_16 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__22 v0
  = case coe v0 of
      C_RawChoice'46'constructor_149 v1 -> coe v1
      _                                 -> MAlonzo.RTE.mazUnreachableError
-- Effect.Choice.RawChoice._∣_
d__'8739'__24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawChoice_16 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8739'__24 ~v0 ~v1 ~v2 v3 ~v4 = du__'8739'__24 v3
du__'8739'__24 :: T_RawChoice_16 -> AgdaAny -> AgdaAny -> AgdaAny
du__'8739'__24 v0 = coe d__'60''124''62'__22 v0 erased
