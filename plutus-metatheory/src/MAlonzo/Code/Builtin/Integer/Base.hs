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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

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
         _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
             case coe v2 of
               _ | coe ltInt (coe v2) (coe (0 :: Integer)) ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Data.Integer.Base.d_pred_312 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v1) (coe v2))
               _ -> coe v3
         0 -> coe v3
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
-- Builtin.Integer.Base.quotMaybe
agdaQuotientInteger ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10 () Integer
agdaQuotientInteger = coe d_quotMaybe_86
d_quotMaybe_86 :: Integer -> Integer -> Maybe Integer
d_quotMaybe_86 v0 v1
  = let v2
          = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
              (coe v1) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe du_quot_12 (coe v0) (coe v1)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.Integer.Base.remMaybe
agdaRemainderInteger ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10 () Integer
agdaRemainderInteger = coe d_remMaybe_112
d_remMaybe_112 :: Integer -> Integer -> Maybe Integer
d_remMaybe_112 v0 v1
  = let v2
          = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
              (coe v1) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe du_rem_24 (coe v0) (coe v1)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.Integer.Base.divModMaybe
d_divModMaybe_138 ::
  Integer -> Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_divModMaybe_138 v0 v1
  = let v2
          = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
              (coe v1) (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe du_divMod_56 (coe v0) (coe v1)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.Integer.Base.divMaybe
agdaDivideInteger ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10 () Integer
agdaDivideInteger = coe d_divMaybe_164
d_divMaybe_164 :: Integer -> Integer -> Maybe Integer
d_divMaybe_164 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_map_64
      (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
      (d_divModMaybe_138 (coe v0) (coe v1))
-- Builtin.Integer.Base.modMaybe
agdaModInteger ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Maybe.T_Maybe_10 () Integer
agdaModInteger = coe d_modMaybe_170
d_modMaybe_170 :: Integer -> Integer -> Maybe Integer
d_modMaybe_170 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_map_64
      (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
      (d_divModMaybe_138 (coe v0) (coe v1))
