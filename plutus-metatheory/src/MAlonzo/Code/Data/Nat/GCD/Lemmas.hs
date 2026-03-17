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

module MAlonzo.Code.Data.Nat.GCD.Lemmas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties

-- Data.Nat.GCD.Lemmas.comm-factor
d_comm'45'factor_14 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm'45'factor_14 = erased
-- Data.Nat.GCD.Lemmas.distrib-comm₂
d_distrib'45'comm'8322'_30 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'45'comm'8322'_30 = erased
-- Data.Nat.GCD.Lemmas.lem₀
d_lem'8320'_50 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8320'_50 = erased
-- Data.Nat.GCD.Lemmas.lem₁
d_lem'8321'_70 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_lem'8321'_70 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''8242'_6152
      (coe addInt (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v1))
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe
            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3550 (coe v0))))
-- Data.Nat.GCD.Lemmas.times2
d_times2_78 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_times2_78 = erased
-- Data.Nat.GCD.Lemmas.times2′
d_times2'8242'_88 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_times2'8242'_88 = erased
-- Data.Nat.GCD.Lemmas.lem₂
d_lem'8322'_102 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8322'_102 = erased
-- Data.Nat.GCD.Lemmas.distrib₃
d_distrib'8323'_124 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'8323'_124 = erased
-- Data.Nat.GCD.Lemmas.lem₃₁
d_lem'8323''8321'_142 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8323''8321'_142 = erased
-- Data.Nat.GCD.Lemmas.+-assoc-comm
d_'43''45'assoc'45'comm_160 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc'45'comm_160 = erased
-- Data.Nat.GCD.Lemmas.*-on-right
d_'42''45'on'45'right_184 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'on'45'right_184 = erased
-- Data.Nat.GCD.Lemmas.*-on-left
d_'42''45'on'45'left_206 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'on'45'left_206 = erased
-- Data.Nat.GCD.Lemmas.+-on-right
d_'43''45'on'45'right_228 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'on'45'right_228 = erased
-- Data.Nat.GCD.Lemmas.+-on-left
d_'43''45'on'45'left_250 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'on'45'left_250 = erased
-- Data.Nat.GCD.Lemmas.+-assoc-comm′
d_'43''45'assoc'45'comm'8242'_292 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc'45'comm'8242'_292 = erased
-- Data.Nat.GCD.Lemmas.lem₃₂
d_lem'8323''8322'_314 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8323''8322'_314 = erased
-- Data.Nat.GCD.Lemmas.mid-to-right
d_mid'45'to'45'right_334 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mid'45'to'45'right_334 = erased
-- Data.Nat.GCD.Lemmas.mid-to-left
d_mid'45'to'45'left_350 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mid'45'to'45'left_350 = erased
-- Data.Nat.GCD.Lemmas.lem₃
d_lem'8323'_372 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8323'_372 = erased
-- Data.Nat.GCD.Lemmas._.y
d_y_390 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_y_390 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_y_390 v1 v2
du_y_390 :: Integer -> Integer -> Integer
du_y_390 v0 v1
  = coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Nat.GCD.Lemmas.lem₄
d_lem'8324'_412 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8324'_412 = erased
-- Data.Nat.GCD.Lemmas.lem₅
d_lem'8325'_438 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8325'_438 = erased
-- Data.Nat.GCD.Lemmas.lem₆
d_lem'8326'_464 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8326'_464 = erased
-- Data.Nat.GCD.Lemmas._.y
d_y_482 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_y_482 ~v0 v1 ~v2 v3 ~v4 ~v5 = du_y_482 v1 v3
du_y_482 :: Integer -> Integer -> Integer
du_y_482 v0 v1
  = coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Nat.GCD.Lemmas.lem₇
d_lem'8327'_498 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8327'_498 = erased
-- Data.Nat.GCD.Lemmas.lem₈
d_lem'8328'_528 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8328'_528 = erased
-- Data.Nat.GCD.Lemmas._.lemma
d_lemma_550 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_550 = erased
-- Data.Nat.GCD.Lemmas.lem₉
d_lem'8329'_570 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8329'_570 = erased
-- Data.Nat.GCD.Lemmas._.lem
d_lem_598 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem_598 = erased
-- Data.Nat.GCD.Lemmas._.lemma
d_lemma_606 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_606 = erased
-- Data.Nat.GCD.Lemmas.lem₁₀
d_lem'8321''8320'_630 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8321''8320'_630 = erased
-- Data.Nat.GCD.Lemmas._.a
d_a_650 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_a_650 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_a_650 v0
du_a_650 :: Integer -> Integer
du_a_650 v0 = coe addInt (coe (1 :: Integer)) (coe v0)
-- Data.Nat.GCD.Lemmas._.*-assoc₄₃
d_'42''45'assoc'8324''8323'_660 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc'8324''8323'_660 = erased
-- Data.Nat.GCD.Lemmas.lem₁₁
d_lem'8321''8321'_692 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8321''8321'_692 = erased
