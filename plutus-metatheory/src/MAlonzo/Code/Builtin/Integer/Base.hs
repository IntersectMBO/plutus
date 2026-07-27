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

module MAlonzo.Code.Builtin.Integer.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sign.Base

-- Builtin.Integer.Base.quot
d_quot_12 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_quot_12 v0 v1 ~v2 = du_quot_12 v0 v1
du_quot_12 :: Integer -> Integer -> Integer
du_quot_12 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe
         MAlonzo.Code.Data.Sign.Base.d__'42'__14
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v1)))
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__318
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Builtin.Integer.Base.rem
d_rem_24 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_rem_24 v0 v1 ~v2 = du_rem_24 v0 v1
du_rem_24 :: Integer -> Integer -> Integer
du_rem_24 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'9667'__238
      (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'37'__330
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
-- Builtin.Integer.Base.divModFixup
d_divModFixup_30 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_divModFixup_30 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1) in
    coe
      (case coe v1 of
         _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
             case coe v2 of
               _ | coe ltInt (coe v2) (coe (0 :: Integer)) ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Data.Integer.Base.d_pred_312 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v2))
               _ -> coe v3
         _ -> case coe v2 of
                _ | coe geqInt (coe v2) (coe (0 :: Integer)) ->
                    coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Integer.Base.d_pred_312 (coe v0))
                      (coe MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v2))
                _ -> coe v3)
-- Builtin.Integer.Base.divMod
d_divMod_56 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_divMod_56 v0 v1 ~v2 = du_divMod_56 v0 v1
du_divMod_56 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_divMod_56 v0 v1
  = coe
      d_divModFixup_30 (coe du_quot_12 (coe v0) (coe v1))
      (coe du_rem_24 (coe v0) (coe v1)) (coe v1)
-- Builtin.Integer.Base.div
d_div_68 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_div_68 v0 v1 ~v2 = du_div_68 v0 v1
du_div_68 :: Integer -> Integer -> Integer
du_div_68 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_divMod_56 (coe v0) (coe v1))
-- Builtin.Integer.Base.mod
d_mod_80 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_mod_80 v0 v1 ~v2 = du_mod_80 v0 v1
du_mod_80 :: Integer -> Integer -> Integer
du_mod_80 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe du_divMod_56 (coe v0) (coe v1))
