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

module MAlonzo.Code.Function.Nary.NonDependent where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Fin.Base qualified
import MAlonzo.Code.Data.Product.Nary.NonDependent qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Level qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Nary.NonDependent.ltabulate
d_ltabulate_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18) ->
  AgdaAny
d_ltabulate_18 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                (coe
                   d_ltabulate_18 (coe v2)
                   (coe
                      MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v1)
                      (coe MAlonzo.Code.Data.Fin.Base.C_suc_16))))
-- Function.Nary.NonDependent.lreplicate
d_lreplicate_28 ::
  Integer -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny
d_lreplicate_28 v0 v1
  = coe d_ltabulate_18 (coe v0) (coe (\ v2 -> v1))
-- Function.Nary.NonDependent.0ℓs
d_0ℓs_34 :: Integer -> AgdaAny
d_0ℓs_34 v0
  = coe d_lreplicate_28 (coe v0) (coe MAlonzo.Code.Level.d_0ℓ_22)
-- Function.Nary.NonDependent._.g
d_g_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny -> AgdaAny -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_g_52 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_g_52 v1 v5
du_g_52 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_g_52 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8345'_150
      (coe v0) (coe v1)
-- Function.Nary.NonDependent._.Congruentₙ
d_Congruent'8345'_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer -> AgdaAny -> AgdaAny -> () -> AgdaAny -> ()
d_Congruent'8345'_54 = erased
-- Function.Nary.NonDependent._.congₙ
d_cong'8345'_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny ->
  AgdaAny -> () -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong'8345'_60 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_cong'8345'_60 v1
du_cong'8345'_60 :: Integer -> AgdaAny
du_cong'8345'_60 v0
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_curry'8345'_130
      (coe v0)
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216 erased erased)
-- Function.Nary.NonDependent._.g
d_g_84 ::
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
d_g_84 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 v13
  = du_g_84 v4 v5 v10 v11 v12 v13
du_g_84 ::
  Integer ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_g_84 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8345'_150 v1
      (coe
         MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8345'_150 v0
         v2 v3 v4)
      v5
-- Function.Nary.NonDependent._.congAt
d_congAt_100 ::
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
d_congAt_100 = erased
-- Function.Nary.NonDependent._.c
d_c_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  AgdaAny -> AgdaAny -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_c_124 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_c_124 v1 v5
du_c_124 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_c_124 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8345'_150
      (coe v0) (coe v1)
-- Function.Nary.NonDependent._.Injectiveₙ
d_Injective'8345'_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer -> AgdaAny -> AgdaAny -> () -> AgdaAny -> ()
d_Injective'8345'_126 = erased
-- Function.Nary.NonDependent._.injectiveₙ
d_injective'8345'_136 ::
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
d_injective'8345'_136 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_injective'8345'_136 v1
du_injective'8345'_136 :: Integer -> AgdaAny
du_injective'8345'_136 v0
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_toEqual'8345'_236
      (coe v0) erased
