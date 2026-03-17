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

module MAlonzo.Code.Data.Integer.GCD where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.GCD
import qualified MAlonzo.Code.Function.Base

-- Data.Integer.GCD.Algebra.Associative
d_Associative_30 :: (Integer -> Integer -> Integer) -> ()
d_Associative_30 = erased
-- Data.Integer.GCD.Algebra.Commutative
d_Commutative_34 :: (Integer -> Integer -> Integer) -> ()
d_Commutative_34 = erased
-- Data.Integer.GCD.Algebra.LeftZero
d_LeftZero_84 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftZero_84 = erased
-- Data.Integer.GCD.Algebra.RightZero
d_RightZero_114 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_RightZero_114 = erased
-- Data.Integer.GCD.Algebra.Zero
d_Zero_134 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Zero_134 = erased
-- Data.Integer.GCD.gcd
d_gcd_136 :: Integer -> Integer -> Integer
d_gcd_136 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd_152
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
-- Data.Integer.GCD.gcd[i,j]∣i
d_gcd'91'i'44'j'93''8739'i_146 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'i'44'j'93''8739'i_146 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd'91'm'44'n'93''8739'm_248
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
-- Data.Integer.GCD.gcd[i,j]∣j
d_gcd'91'i'44'j'93''8739'j_156 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'i'44'j'93''8739'j_156 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd'91'm'44'n'93''8739'n_278
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
-- Data.Integer.GCD.gcd-greatest
d_gcd'45'greatest_168 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'45'greatest_168 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd'45'greatest_310
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v5 v6 -> v6) MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
         v2 v0)
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (\ v5 v6 -> v5)
         v2 (d_gcd_136 (coe v0) (coe v1)))
      (coe v3) (coe v4)
-- Data.Integer.GCD.gcd[0,0]≡0
d_gcd'91'0'44'0'93''8801'0_174 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'91'0'44'0'93''8801'0_174 = erased
-- Data.Integer.GCD.gcd[i,j]≡0⇒i≡0
d_gcd'91'i'44'j'93''8801'0'8658'i'8801'0_180 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'91'i'44'j'93''8801'0'8658'i'8801'0_180 = erased
-- Data.Integer.GCD.gcd[i,j]≡0⇒j≡0
d_gcd'91'i'44'j'93''8801'0'8658'j'8801'0_192 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'91'i'44'j'93''8801'0'8658'j'8801'0_192 = erased
-- Data.Integer.GCD.gcd-comm
d_gcd'45'comm_198 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'comm_198 = erased
-- Data.Integer.GCD.gcd-assoc
d_gcd'45'assoc_204 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'assoc_204 = erased
-- Data.Integer.GCD.gcd-zeroˡ
d_gcd'45'zero'737'_212 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'zero'737'_212 = erased
-- Data.Integer.GCD.gcd-zeroʳ
d_gcd'45'zero'691'_216 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'zero'691'_216 = erased
-- Data.Integer.GCD.gcd-zero
d_gcd'45'zero_220 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gcd'45'zero_220
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
