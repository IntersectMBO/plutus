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

module MAlonzo.Code.Data.Integer.Coprimality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Coprimality
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Integer.Coprimality.Coprime
d_Coprime_6 :: Integer -> Integer -> ()
d_Coprime_6 = erased
-- Data.Integer.Coprimality.sym
d_sym_8 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_8 = erased
-- Data.Integer.Coprimality.coprime?
d_coprime'63'_10 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_coprime'63'_10 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Coprimality.d_coprime'63'_70
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
-- Data.Integer.Coprimality.coprime-divisor
d_coprime'45'divisor_22 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_coprime'45'divisor_22 v0 v1 v2 ~v3 v4
  = du_coprime'45'divisor_22 v0 v1 v2 v4
du_coprime'45'divisor_22 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_coprime'45'divisor_22 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Coprimality.du_coprime'45'divisor_134
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (\ v4 v5 -> v4)
         v0 v2)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5) MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
         v0 v1)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5) MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
         v0 v2)
      (coe v3)
