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

module MAlonzo.Code.Data.Nat.GeneralisedArithmetic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- Data.Nat.GeneralisedArithmetic.fold
d_fold_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> Integer -> AgdaAny
d_fold_10 ~v0 ~v1 v2 v3 v4 = du_fold_10 v2 v3 v4
du_fold_10 :: AgdaAny -> (AgdaAny -> AgdaAny) -> Integer -> AgdaAny
du_fold_10 v0 v1 v2
  = case coe v2 of
      0 -> coe v0
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe (coe v1 (coe du_fold_10 (coe v0) (coe v1) (coe v3)))
-- Data.Nat.GeneralisedArithmetic.iterate
d_iterate_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> Integer -> AgdaAny
d_iterate_22 ~v0 ~v1 v2 v3 v4 = du_iterate_22 v2 v3 v4
du_iterate_22 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> Integer -> AgdaAny
du_iterate_22 v0 v1 v2
  = case coe v2 of
      0 -> coe v1
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe (coe du_iterate_22 (coe v0) (coe v0 v1) (coe v3))
-- Data.Nat.GeneralisedArithmetic.add
d_add_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> Integer -> AgdaAny -> AgdaAny
d_add_38 ~v0 ~v1 ~v2 v3 v4 v5 = du_add_38 v3 v4 v5
du_add_38 :: (AgdaAny -> AgdaAny) -> Integer -> AgdaAny -> AgdaAny
du_add_38 v0 v1 v2 = coe du_fold_10 (coe v2) (coe v0) (coe v1)
-- Data.Nat.GeneralisedArithmetic.mul
d_mul_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny -> AgdaAny
d_mul_54 ~v0 ~v1 v2 ~v3 v4 v5 v6 = du_mul_54 v2 v4 v5 v6
du_mul_54 ::
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny -> AgdaAny
du_mul_54 v0 v1 v2 v3
  = coe du_fold_10 (coe v0) (coe v1 v3) (coe v2)
-- Data.Nat.GeneralisedArithmetic.fold-+
d_fold'45''43'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45''43'_76 = erased
-- Data.Nat.GeneralisedArithmetic.fold-k
d_fold'45'k_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'k_98 = erased
-- Data.Nat.GeneralisedArithmetic.fold-*
d_fold'45''42'_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45''42'_120 = erased
-- Data.Nat.GeneralisedArithmetic.fold-pull
d_fold'45'pull_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'pull_156 = erased
-- Data.Nat.GeneralisedArithmetic.iterate-is-fold
d_iterate'45'is'45'fold_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iterate'45'is'45'fold_184 = erased
-- Data.Nat.GeneralisedArithmetic.id-is-fold
d_id'45'is'45'fold_198 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_id'45'is'45'fold_198 = erased
-- Data.Nat.GeneralisedArithmetic.+-is-fold
d_'43''45'is'45'fold_206 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'is'45'fold_206 = erased
-- Data.Nat.GeneralisedArithmetic.*-is-fold
d_'42''45'is'45'fold_216 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'is'45'fold_216 = erased
-- Data.Nat.GeneralisedArithmetic.^-is-fold
d_'94''45'is'45'fold_230 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'is'45'fold_230 = erased
-- Data.Nat.GeneralisedArithmetic.*+-is-fold
d_'42''43''45'is'45'fold_246 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''43''45'is'45'fold_246 = erased
-- Data.Nat.GeneralisedArithmetic.^*-is-fold
d_'94''42''45'is'45'fold_270 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''42''45'is'45'fold_270 = erased
