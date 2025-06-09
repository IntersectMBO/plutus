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

module MAlonzo.Code.Level where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Level.Lift
d_Lift_8 a0 a1 a2 = ()
newtype T_Lift_8 = C_lift_20 AgdaAny
-- Level.Lift.lower
d_lower_18 :: T_Lift_8 -> AgdaAny
d_lower_18 v0
  = case coe v0 of
      C_lift_20 v1 -> coe v1
      _            -> MAlonzo.RTE.mazUnreachableError
-- Level.0ℓ
d_0ℓ_22 :: MAlonzo.Code.Agda.Primitive.T_Level_18
d_0ℓ_22 = coe MAlonzo.Code.Agda.Primitive.d_lzero_20
-- Level.levelOfType
d_levelOfType_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_levelOfType_26 v0 ~v1 = du_levelOfType_26 v0
du_levelOfType_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18
du_levelOfType_26 v0 = coe v0
-- Level.levelOfTerm
d_levelOfTerm_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_levelOfTerm_34 v0 ~v1 ~v2 = du_levelOfTerm_34 v0
du_levelOfTerm_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18
du_levelOfTerm_34 v0 = coe v0
