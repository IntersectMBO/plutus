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

module MAlonzo.Code.Function.Strict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Strict
import qualified MAlonzo.Code.Agda.Primitive

-- Function.Strict._$!_
d__'36''33'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'36''33'__20 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'36''33'__20 v4 v5
du__'36''33'__20 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'36''33'__20 v0 v1 = coe seq (coe v1) (coe v0 v1)
-- Function.Strict._!|>_
d__'33''124''62'__34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'33''124''62'__34 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'33''124''62'__34 v4 v5
du__'33''124''62'__34 :: AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'33''124''62'__34 v0 v1
  = coe du__'36''33'__20 (coe v1) (coe v0)
-- Function.Strict.seq
d_seq_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d_seq_36 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_seq_36 v4 v5
du_seq_36 :: AgdaAny -> AgdaAny -> AgdaAny
du_seq_36 v0 v1 = coe seq (coe v0) (coe v1)
-- Function.Strict.seq-≡
d_seq'45''8801'_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_seq'45''8801'_48 = erased
-- Function.Strict.force′
d_force'8242'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_force'8242'_56 v0 ~v1 v2 ~v3 = du_force'8242'_56 v0 v2
du_force'8242'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_force'8242'_56 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Strict.d_primForce_18 v0 v1 erased erased
-- Function.Strict.force′-≡
d_force'8242''45''8801'_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_force'8242''45''8801'_62 = erased
-- Function.Strict._$!′_
d__'36''33''8242'__64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'36''33''8242'__64 ~v0 ~v1 ~v2 ~v3 = du__'36''33''8242'__64
du__'36''33''8242'__64 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'36''33''8242'__64 = coe du__'36''33'__20
-- Function.Strict._!|>′_
d__'33''124''62''8242'__66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'33''124''62''8242'__66 ~v0 ~v1 ~v2 ~v3
  = du__'33''124''62''8242'__66
du__'33''124''62''8242'__66 ::
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'33''124''62''8242'__66 = coe du__'33''124''62'__34
