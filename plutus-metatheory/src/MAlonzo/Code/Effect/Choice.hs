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

module MAlonzo.Code.Effect.Choice where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Effect.Choice.RawChoice
d_RawChoice_16 a0 a1 a2 = ()
newtype T_RawChoice_16
  = C_constructor_26 (() -> AgdaAny -> AgdaAny -> AgdaAny)
-- Effect.Choice.RawChoice._<|>_
d__'60''124''62'__22 ::
  T_RawChoice_16 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__22 v0
  = case coe v0 of
      C_constructor_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Choice.RawChoice._∣_
d__'8739'__24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawChoice_16 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8739'__24 ~v0 ~v1 ~v2 v3 ~v4 = du__'8739'__24 v3
du__'8739'__24 :: T_RawChoice_16 -> AgdaAny -> AgdaAny -> AgdaAny
du__'8739'__24 v0 = coe d__'60''124''62'__22 v0 erased
