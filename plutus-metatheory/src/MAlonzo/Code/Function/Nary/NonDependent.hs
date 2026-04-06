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

module MAlonzo.Code.Function.Nary.NonDependent where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Nary.NonDependent
import qualified MAlonzo.Code.Function.Base

-- Function.Nary.NonDependent._.g
d_g_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny -> AgdaAny -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_g_32 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_g_32 v1 v5
du_g_32 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_g_32 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8345'_170
      (coe v0) (coe v1)
-- Function.Nary.NonDependent._.Congruentₙ
d_Congruent'8345'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer -> AgdaAny -> AgdaAny -> () -> AgdaAny -> ()
d_Congruent'8345'_34 = erased
-- Function.Nary.NonDependent._.congₙ
d_cong'8345'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny ->
  AgdaAny -> () -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong'8345'_40 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_cong'8345'_40 v1
du_cong'8345'_40 :: Integer -> AgdaAny
du_cong'8345'_40 v0
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_curry'8345'_150
      (coe v0)
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216 erased erased)
-- Function.Nary.NonDependent._.g
d_g_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_g_64 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 v13
  = du_g_64 v4 v5 v10 v11 v12 v13
du_g_64 ::
  Integer ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_g_64 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8345'_170 v1
      (coe
         MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8345'_170 v0
         v2 v3 v4)
      v5
-- Function.Nary.NonDependent._.congAt
d_congAt_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_congAt_80 = erased
-- Function.Nary.NonDependent._.c
d_c_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny -> AgdaAny -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_c_104 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_c_104 v1 v5
du_c_104 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_c_104 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8345'_170
      (coe v0) (coe v1)
-- Function.Nary.NonDependent._.Injectiveₙ
d_Injective'8345'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer -> AgdaAny -> AgdaAny -> () -> AgdaAny -> ()
d_Injective'8345'_106 = erased
-- Function.Nary.NonDependent._.injectiveₙ
d_injective'8345'_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  () ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_injective'8345'_116 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_injective'8345'_116 v1
du_injective'8345'_116 :: Integer -> AgdaAny
du_injective'8345'_116 v0
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_toEqual'8345'_256
      (coe v0) erased
