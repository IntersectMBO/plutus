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

module MAlonzo.Code.Data.Nat.DivMod.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Nat.DivMod.Core.mod-cong₃
d_mod'45'cong'8323'_18 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'45'cong'8323'_18 = erased
-- Data.Nat.DivMod.Core.modₕ-skipTo0
d_mod'8341''45'skipTo0_28 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8341''45'skipTo0_28 = erased
-- Data.Nat.DivMod.Core.a[modₕ]1≡0
d_a'91'mod'8341''93'1'8801'0_50 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'91'mod'8341''93'1'8801'0_50 = erased
-- Data.Nat.DivMod.Core.n[modₕ]n≡0
d_n'91'mod'8341''93'n'8801'0_58 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'91'mod'8341''93'n'8801'0_58 = erased
-- Data.Nat.DivMod.Core.a[modₕ]n<n
d_a'91'mod'8341''93'n'60'n_70 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_a'91'mod'8341''93'n'60'n_70 v0 v1 v2
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0)
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                0 -> coe
                       d_a'91'mod'8341''93'n'60'n_70 (coe (0 :: Integer)) (coe v3)
                       (coe v0)
                _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                     coe
                       (coe
                          d_a'91'mod'8341''93'n'60'n_70
                          (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3) (coe v4)))
-- Data.Nat.DivMod.Core.a[modₕ]n≤a
d_a'91'mod'8341''93'n'8804'a_96 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_a'91'mod'8341''93'n'8804'a_96 v0 v1 v2
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0
                (addInt (coe v0) (coe v2)) (0 :: Integer) v2)
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                0 -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                          (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                          (\ v4 v5 v6 ->
                             coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v6))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0 v0 v1
                          (0 :: Integer))
                       (addInt (coe v0) (coe v1))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                          (\ v4 v5 v6 v7 v8 -> v8)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0 v0 v1
                             (0 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0 v0 v1
                             (0 :: Integer))
                          (addInt (coe v0) (coe v1))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                (\ v4 v5 v6 v7 v8 ->
                                   coe
                                     MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                     v7 v8))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0 v0 v1
                                (0 :: Integer))
                             v3 (addInt (coe v0) (coe v1))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                   (\ v4 v5 v6 v7 v8 ->
                                      coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                        v7 v8))
                                v3 v1 (addInt (coe v0) (coe v1))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                      (\ v4 v5 v6 v7 v8 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                           v7 v8))
                                   v1 (addInt (coe v0) (coe v1)) (addInt (coe v0) (coe v1))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                         (coe
                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                      (coe addInt (coe v0) (coe v1)))
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
                                      (coe v1)))
                                (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v3)))
                             (d_a'91'mod'8341''93'n'8804'a_96
                                (coe (0 :: Integer)) (coe v3) (coe v0)))
                          erased)
                _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                             (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                             (\ v5 v6 v7 ->
                                coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v7))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0
                             (addInt (coe v0) (coe v2)) v1 v2)
                          (addInt (coe v0) (coe v1))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                             (\ v5 v6 v7 v8 v9 -> v9)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0
                                (addInt (coe v0) (coe v2)) v1 v2)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0
                                (addInt (coe v0) (coe v2)) v1 v2)
                             (addInt (coe v0) (coe v1))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                   (coe
                                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                   (\ v5 v6 v7 v8 v9 ->
                                      coe
                                        MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                        v8 v9))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0
                                   (addInt (coe v0) (coe v2)) v1 v2)
                                (addInt (coe v0) (coe v1)) (addInt (coe v0) (coe v1))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                   (\ v5 v6 v7 v8 v9 -> v9) (addInt (coe v0) (coe v1))
                                   (addInt (coe v0) (coe v1)) (addInt (coe v0) (coe v1))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                         (coe
                                            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                      (coe addInt (coe v0) (coe v1)))
                                   erased)
                                (d_a'91'mod'8341''93'n'8804'a_96
                                   (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3) (coe v4)))
                             erased)))
-- Data.Nat.DivMod.Core.a≤n⇒a[modₕ]n≡a
d_a'8804'n'8658'a'91'mod'8341''93'n'8801'a_124 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'8804'n'8658'a'91'mod'8341''93'n'8801'a_124 = erased
-- Data.Nat.DivMod.Core.modₕ-idem
d_mod'8341''45'idem_146 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mod'8341''45'idem_146 = erased
-- Data.Nat.DivMod.Core.a+1[modₕ]n≡0⇒a[modₕ]n≡n-1
d_a'43'1'91'mod'8341''93'n'8801'0'8658'a'91'mod'8341''93'n'8801'n'45'1_176 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'43'1'91'mod'8341''93'n'8801'0'8658'a'91'mod'8341''93'n'8801'n'45'1_176
  = erased
-- Data.Nat.DivMod.Core.k<1+a[modₕ]n⇒k≤a[modₕ]n
d_k'60'1'43'a'91'mod'8341''93'n'8658'k'8804'a'91'mod'8341''93'n_216 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_k'60'1'43'a'91'mod'8341''93'n'8658'k'8804'a'91'mod'8341''93'n_216 v0
                                                                    ~v1 v2 v3 v4
  = du_k'60'1'43'a'91'mod'8341''93'n'8658'k'8804'a'91'mod'8341''93'n_216
      v0 v2 v3 v4
du_k'60'1'43'a'91'mod'8341''93'n'8658'k'8804'a'91'mod'8341''93'n_216 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_k'60'1'43'a'91'mod'8341''93'n'8658'k'8804'a'91'mod'8341''93'n_216 v0
                                                                     v1 v2 v3
  = case coe v1 of
      0 -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6 -> coe v6
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                0 -> coe
                       du_k'60'1'43'a'91'mod'8341''93'n'8658'k'8804'a'91'mod'8341''93'n_216
                       (coe (0 :: Integer)) (coe v4) (coe v0) (coe v3)
                _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_k'60'1'43'a'91'mod'8341''93'n'8658'k'8804'a'91'mod'8341''93'n_216
                          (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v4) (coe v5)
                          (coe v3)))
-- Data.Nat.DivMod.Core.1+a[modₕ]n≤1+k⇒a[modₕ]n≤k
d_1'43'a'91'mod'8341''93'n'8804'1'43'k'8658'a'91'mod'8341''93'n'8804'k_260 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'43'a'91'mod'8341''93'n'8804'1'43'k'8658'a'91'mod'8341''93'n'8804'k_260 v0
                                                                           ~v1 v2 v3 ~v4 v5
  = du_1'43'a'91'mod'8341''93'n'8804'1'43'k'8658'a'91'mod'8341''93'n'8804'k_260
      v0 v2 v3 v5
du_1'43'a'91'mod'8341''93'n'8804'1'43'k'8658'a'91'mod'8341''93'n'8804'k_260 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_1'43'a'91'mod'8341''93'n'8804'1'43'k'8658'a'91'mod'8341''93'n'8804'k_260 v0
                                                                            v1 v2 v3
  = case coe v1 of
      0 -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6 -> coe v6
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                0 -> coe
                       du_1'43'a'91'mod'8341''93'n'8804'1'43'k'8658'a'91'mod'8341''93'n'8804'k_260
                       (coe (0 :: Integer)) (coe v4) (coe v0) (coe v3)
                _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_1'43'a'91'mod'8341''93'n'8804'1'43'k'8658'a'91'mod'8341''93'n'8804'k_260
                          (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v4) (coe v5)
                          (coe v3)))
-- Data.Nat.DivMod.Core.a+n[modₕ]n≡a[modₕ]n
d_a'43'n'91'mod'8341''93'n'8801'a'91'mod'8341''93'n_308 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'43'n'91'mod'8341''93'n'8801'a'91'mod'8341''93'n_308 = erased
-- Data.Nat.DivMod.Core._.mod₁
d_mod'8321'_336 ::
  Integer -> Integer -> Integer -> Integer -> Integer -> Integer
d_mod'8321'_336 v0 v1 ~v2 = du_mod'8321'_336 v0 v1
du_mod'8321'_336 ::
  Integer -> Integer -> Integer -> Integer -> Integer
du_mod'8321'_336 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90 v0
      (addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1))
-- Data.Nat.DivMod.Core._.mod₂
d_mod'8322'_338 ::
  Integer -> Integer -> Integer -> Integer -> Integer -> Integer
d_mod'8322'_338 v0 v1 ~v2 = du_mod'8322'_338 v0 v1
du_mod'8322'_338 ::
  Integer -> Integer -> Integer -> Integer -> Integer
du_mod'8322'_338 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d_mod'45'helper_90
      (addInt (coe (1 :: Integer)) (coe v0))
      (addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1))
-- Data.Nat.DivMod.Core.div-cong₃
d_div'45'cong'8323'_358 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_div'45'cong'8323'_358 = erased
-- Data.Nat.DivMod.Core.acc≤divₕ[acc]
d_acc'8804'div'8341''91'acc'93'_368 ::
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_acc'8804'div'8341''91'acc'93'_368 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0)
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                0 -> coe
                       MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v0))
                       (coe
                          d_acc'8804'div'8341''91'acc'93'_368
                          (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1) (coe v4)
                          (coe v1))
                _ -> let v5 = subInt (coe v3) (coe (1 :: Integer)) in
                     coe
                       (coe
                          d_acc'8804'div'8341''91'acc'93'_368 (coe v0) (coe v1) (coe v4)
                          (coe v5)))
-- Data.Nat.DivMod.Core.divₕ-offsetEq
d_div'8341''45'offsetEq_410 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_div'8341''45'offsetEq_410 = erased
-- Data.Nat.DivMod.Core.div-mod-lemma
d_div'45'mod'45'lemma_656 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_div'45'mod'45'lemma_656 = erased
-- Data.Nat.DivMod.Core._.m
d_m_686 :: Integer -> Integer -> Integer -> Integer -> Integer
d_m_686 v0 v1 ~v2 ~v3 = du_m_686 v0 v1
du_m_686 :: Integer -> Integer -> Integer
du_m_686 v0 v1
  = coe addInt (coe addInt (coe (2 :: Integer)) (coe v0)) (coe v1)
-- Data.Nat.DivMod.Core.divₕ-restart
d_div'8341''45'restart_700 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_div'8341''45'restart_700 = erased
-- Data.Nat.DivMod.Core.divₕ-extractAcc
d_div'8341''45'extractAcc_724 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_div'8341''45'extractAcc_724 = erased
-- Data.Nat.DivMod.Core.divₕ-finish
d_div'8341''45'finish_756 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_div'8341''45'finish_756 = erased
-- Data.Nat.DivMod.Core.n[divₕ]n≡1
d_n'91'div'8341''93'n'8801'1_776 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'91'div'8341''93'n'8801'1_776 = erased
-- Data.Nat.DivMod.Core.a[divₕ]1≡a
d_a'91'div'8341''93'1'8801'a_788 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'91'div'8341''93'1'8801'a_788 = erased
-- Data.Nat.DivMod.Core.a*n[divₕ]n≡a
d_a'42'n'91'div'8341''93'n'8801'a_802 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'42'n'91'div'8341''93'n'8801'a_802 = erased
-- Data.Nat.DivMod.Core.+-distrib-divₕ
d_'43''45'distrib'45'div'8341'_824 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'45'div'8341'_824 = erased
-- Data.Nat.DivMod.Core._.case
d_case_870 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_case_870 ~v0 v1 ~v2 v3 v4 = du_case_870 v1 v3 v4
du_case_870 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_case_870 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
      (coe
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe
                  MAlonzo.Code.Data.Nat.Properties.du_'43''45'cancel'737''45''8804'_3556
                  (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))
               (coe
                  MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636 (coe v1)))))
-- Data.Nat.DivMod.Core.divₕ-mono-≤
d_div'8341''45'mono'45''8804'_886 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_div'8341''45'mono'45''8804'_886 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             d_acc'8804'div'8341''91'acc'93'_368
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60 v0
                (addInt (coe v1) (coe v4)) (0 :: Integer) v4)
             (coe addInt (coe v1) (coe v5)) (coe v3) (coe v5)
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v10
        -> let v11 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v12 = subInt (coe v3) (coe (1 :: Integer)) in
              coe
                (let v13
                       = seq
                           (coe v7)
                           (let v13
                                  = coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      (\ v13 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                           (coe addInt (coe (1 :: Integer)) (coe v4)))
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                            (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v2))) in
                            coe
                              (case coe v13 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                   -> if coe v14
                                        then coe
                                               seq (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                     (\ v16 v17 v18 ->
                                                        coe
                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                          v18))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                     v0 (addInt (coe v1) (coe v4)) v2 v4)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                     (addInt (coe (1 :: Integer)) (coe v0)) v1 v12
                                                     v1)
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                                     (\ v16 v17 v18 v19 v20 -> v20)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                        v0 (addInt (coe v1) (coe v4)) v2 v4)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                        (addInt (coe (1 :: Integer)) (coe v0))
                                                        (addInt (coe v1) (coe v4))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                           v11 v4)
                                                        (addInt (coe v1) (coe v4)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                        (addInt (coe (1 :: Integer)) (coe v0)) v1
                                                        v12 v1)
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                           (\ v16 v17 v18 v19 v20 ->
                                                              coe
                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                v19 v20))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                           (addInt (coe (1 :: Integer)) (coe v0))
                                                           (addInt (coe v1) (coe v4))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                              v11 v4)
                                                           (addInt (coe v1) (coe v4)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                           (addInt (coe (1 :: Integer)) (coe v0)) v1
                                                           v12 v1)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                           (addInt (coe (1 :: Integer)) (coe v0)) v1
                                                           v12 v1)
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                              (coe
                                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                              (addInt (coe (1 :: Integer)) (coe v0))
                                                              v1 v12 v1))
                                                        (d_div'8341''45'mono'45''8804'_886
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v0))
                                                           (coe (0 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                              v11 v4)
                                                           (coe v12) (coe addInt (coe v1) (coe v4))
                                                           (coe v1)
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                              (coe
                                                                 MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
                                                                 (coe v11) (coe v4))
                                                              (coe v10))
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                              (coe v1))))
                                                     erased))
                                        else coe
                                               seq (coe v15)
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                     (\ v16 v17 v18 ->
                                                        coe
                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                          v18))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                     v0 (addInt (coe v1) (coe v4)) v2 v4)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                     (addInt (coe (1 :: Integer)) (coe v0)) v1 v12
                                                     v1)
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                                     (\ v16 v17 v18 v19 v20 -> v20)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                        v0 (addInt (coe v1) (coe v4)) v2 v4)
                                                     v0
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                        (addInt (coe (1 :: Integer)) (coe v0)) v1
                                                        v12 v1)
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                           (\ v16 v17 v18 v19 v20 ->
                                                              coe
                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                v19 v20))
                                                        v0 (addInt (coe (1 :: Integer)) (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                           (addInt (coe (1 :: Integer)) (coe v0)) v1
                                                           v12 v1)
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                              (coe
                                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                              (\ v16 v17 v18 v19 v20 ->
                                                                 coe
                                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                   v19 v20))
                                                           (addInt (coe (1 :: Integer)) (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                              (addInt (coe (1 :: Integer)) (coe v0))
                                                              v1 v12 v1)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                              (addInt (coe (1 :: Integer)) (coe v0))
                                                              v1 v12 v1)
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                              (coe
                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                 (addInt
                                                                    (coe (1 :: Integer)) (coe v0))
                                                                 v1 v12 v1))
                                                           (d_acc'8804'div'8341''91'acc'93'_368
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v0))
                                                              (coe v1) (coe v12) (coe v1)))
                                                        (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                                           (coe v0)))
                                                     erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError)) in
                 coe
                   (case coe v4 of
                      0 -> case coe v5 of
                             0 -> case coe v7 of
                                    MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                      -> let v15 = 0 :: Integer in
                                         coe
                                           (let v16
                                                  = coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                      (\ v16 ->
                                                         coe
                                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                           (coe (1 :: Integer)))
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                            (coe (1 :: Integer)) (coe v2))) in
                                            coe
                                              (case coe v16 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                   -> if coe v17
                                                        then coe
                                                               seq (coe v18)
                                                               (coe
                                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                     (\ v19 v20 v21 ->
                                                                        coe
                                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                          v21))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                     v0 v1 v2 v15)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                     (addInt
                                                                        (coe (1 :: Integer))
                                                                        (coe v0))
                                                                     v1 v12 v1)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                                                     (\ v19 v20 v21 v22 v23 -> v23)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        v0 v1 v2 v15)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        (addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v0))
                                                                        v1
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                           v11 v15)
                                                                        v1)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        (addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v0))
                                                                        v1 v12 v1)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                           (coe
                                                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                           (\ v19 v20 v21 v22 v23 ->
                                                                              coe
                                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                v22 v23))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           v1
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                              v11 v15)
                                                                           v1)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           v1 v12 v1)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           v1 v12 v1)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                              (addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              v1 v12 v1))
                                                                        (d_div'8341''45'mono'45''8804'_886
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                              v11 v15)
                                                                           (coe v12) (coe v1)
                                                                           (coe v1)
                                                                           (coe
                                                                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
                                                                                 (coe v11)
                                                                                 (coe v15))
                                                                              (coe v10))
                                                                           (coe
                                                                              MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                                              (coe v1))))
                                                                     erased))
                                                        else coe
                                                               seq (coe v18)
                                                               (coe
                                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                     (\ v19 v20 v21 ->
                                                                        coe
                                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                          v21))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                     v0 v1 v2 v15)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                     (addInt
                                                                        (coe (1 :: Integer))
                                                                        (coe v0))
                                                                     v1 v12 v1)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                                                     (\ v19 v20 v21 v22 v23 -> v23)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        v0 v1 v2 v15)
                                                                     v0
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        (addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v0))
                                                                        v1 v12 v1)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                           (coe
                                                                              MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                           (\ v19 v20 v21 v22 v23 ->
                                                                              coe
                                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                v22 v23))
                                                                        v0
                                                                        (addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v0))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           v1 v12 v1)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                              (\ v19 v20 v21 v22
                                                                                 v23 ->
                                                                                 coe
                                                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                   v22 v23))
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                              (addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              v1 v12 v1)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                              (addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              v1 v12 v1)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                                 (addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v0))
                                                                                 v1 v12 v1))
                                                                           (d_acc'8804'div'8341''91'acc'93'_368
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              (coe v1) (coe v12)
                                                                              (coe v1)))
                                                                        (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                                                           (coe v0)))
                                                                     erased))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> coe v13
                      _ -> let v14 = subInt (coe v4) (coe (1 :: Integer)) in
                           coe
                             (case coe v5 of
                                0 -> coe
                                       seq (coe v7)
                                       (let v15
                                              = coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                  (\ v15 ->
                                                     coe
                                                       MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                       (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                        (coe addInt (coe (1 :: Integer)) (coe v4))
                                                        (coe v2))) in
                                        coe
                                          (case coe v15 of
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                               -> if coe v16
                                                    then coe
                                                           seq (coe v17)
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                              (coe
                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                 (\ v18 v19 v20 ->
                                                                    coe
                                                                      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                      v20))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                 v0 (addInt (coe v1) (coe v4)) v2
                                                                 v4)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                 (addInt
                                                                    (coe (1 :: Integer)) (coe v0))
                                                                 v1 v12 v1)
                                                              (coe
                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                                                 (\ v18 v19 v20 v21 v22 -> v22)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                    v0 (addInt (coe v1) (coe v4)) v2
                                                                    v4)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                    (addInt
                                                                       (coe (1 :: Integer))
                                                                       (coe v0))
                                                                    (addInt (coe v1) (coe v4))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                       v11 v4)
                                                                    (addInt (coe v1) (coe v4)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                    (addInt
                                                                       (coe (1 :: Integer))
                                                                       (coe v0))
                                                                    v1 v12 v1)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                       (\ v18 v19 v20 v21 v22 ->
                                                                          coe
                                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                            v21 v22))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                       (addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v0))
                                                                       (addInt (coe v1) (coe v4))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                          v11 v4)
                                                                       (addInt (coe v1) (coe v4)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                       (addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v0))
                                                                       v1 v12 v1)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                       (addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v0))
                                                                       v1 v12 v1)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                          (addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe v0))
                                                                          v1 v12 v1))
                                                                    (d_div'8341''45'mono'45''8804'_886
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v0))
                                                                       (coe (0 :: Integer))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                          v11 v4)
                                                                       (coe v12)
                                                                       (coe
                                                                          addInt (coe v1) (coe v4))
                                                                       (coe v1)
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
                                                                             (coe v11) (coe v4))
                                                                          (coe v10))
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                                          (coe v1))))
                                                                 erased))
                                                    else coe
                                                           seq (coe v17)
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                              (coe
                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                 (\ v18 v19 v20 ->
                                                                    coe
                                                                      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                      v20))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                 v0 (addInt (coe v1) (coe v4)) v2
                                                                 v4)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                 (addInt
                                                                    (coe (1 :: Integer)) (coe v0))
                                                                 v1 v12 v1)
                                                              (coe
                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                                                 (\ v18 v19 v20 v21 v22 -> v22)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                    v0 (addInt (coe v1) (coe v4)) v2
                                                                    v4)
                                                                 v0
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                    (addInt
                                                                       (coe (1 :: Integer))
                                                                       (coe v0))
                                                                    v1 v12 v1)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                       (\ v18 v19 v20 v21 v22 ->
                                                                          coe
                                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                            v21 v22))
                                                                    v0
                                                                    (addInt
                                                                       (coe (1 :: Integer))
                                                                       (coe v0))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                       (addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v0))
                                                                       v1 v12 v1)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                          (coe
                                                                             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                          (\ v18 v19 v20 v21 v22 ->
                                                                             coe
                                                                               MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                               v21 v22))
                                                                       (addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v0))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                          (addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe v0))
                                                                          v1 v12 v1)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                          (addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe v0))
                                                                          v1 v12 v1)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                                             (coe
                                                                                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                             (addInt
                                                                                (coe (1 :: Integer))
                                                                                (coe v0))
                                                                             v1 v12 v1))
                                                                       (d_acc'8804'div'8341''91'acc'93'_368
                                                                          (coe
                                                                             addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe v0))
                                                                          (coe v1) (coe v12)
                                                                          (coe v1)))
                                                                    (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                                                       (coe v0)))
                                                                 erased))
                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                _ -> let v15 = subInt (coe v5) (coe (1 :: Integer)) in
                                     coe
                                       (case coe v7 of
                                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v18
                                            -> coe
                                                 d_div'8341''45'mono'45''8804'_886 (coe v0)
                                                 (coe addInt (coe (1 :: Integer)) (coe v1))
                                                 (coe v11) (coe v12) (coe v14) (coe v15) (coe v10)
                                                 (coe v18)
                                          MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                            -> let v17
                                                     = coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                         (\ v17 ->
                                                            coe
                                                              MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v4)))
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v4))
                                                               (coe v2))) in
                                               coe
                                                 (case coe v17 of
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                      -> if coe v18
                                                           then coe
                                                                  seq (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                                                        (coe
                                                                           MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                        (\ v20 v21 v22 ->
                                                                           coe
                                                                             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                             v22))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        v0
                                                                        (addInt (coe v1) (coe v4))
                                                                        v2 v4)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        (addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v0))
                                                                        v1 v12 v1)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                                                        (\ v20 v21 v22 v23 v24 ->
                                                                           v24)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           v0
                                                                           (addInt
                                                                              (coe v1) (coe v4))
                                                                           v2 v4)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           (addInt
                                                                              (coe v1) (coe v4))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                              v11 v4)
                                                                           (addInt
                                                                              (coe v1) (coe v4)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           v1 v12 v1)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                              (\ v20 v21 v22 v23
                                                                                 v24 ->
                                                                                 coe
                                                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                   v23 v24))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                              (addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              (addInt
                                                                                 (coe v1) (coe v4))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                 v11 v4)
                                                                              (addInt
                                                                                 (coe v1) (coe v4)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                              (addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              v1 v12 v1)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                              (addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              v1 v12 v1)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                                 (addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v0))
                                                                                 v1 v12 v1))
                                                                           (d_div'8341''45'mono'45''8804'_886
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              (coe (0 :: Integer))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                 v11 v4)
                                                                              (coe v12)
                                                                              (coe
                                                                                 addInt (coe v1)
                                                                                 (coe v4))
                                                                              (coe v1)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
                                                                                    (coe v11)
                                                                                    (coe v4))
                                                                                 (coe v10))
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                                                                                 (coe v1))))
                                                                        erased))
                                                           else coe
                                                                  seq (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                                                        (coe
                                                                           MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                        (\ v20 v21 v22 ->
                                                                           coe
                                                                             MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                             v22))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        v0
                                                                        (addInt (coe v1) (coe v4))
                                                                        v2 v4)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                        (addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v0))
                                                                        v1 v12 v1)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                                                                        (\ v20 v21 v22 v23 v24 ->
                                                                           v24)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           v0
                                                                           (addInt
                                                                              (coe v1) (coe v4))
                                                                           v2 v4)
                                                                        v0
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           v1 v12 v1)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                              (\ v20 v21 v22 v23
                                                                                 v24 ->
                                                                                 coe
                                                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                   v23 v24))
                                                                           v0
                                                                           (addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                              (addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              v1 v12 v1)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                                                                                 (\ v20 v21 v22 v23
                                                                                    v24 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                      v23 v24))
                                                                              (addInt
                                                                                 (coe
                                                                                    (1 :: Integer))
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                                 (addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v0))
                                                                                 v1 v12 v1)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                                 (addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v0))
                                                                                 v1 v12 v1)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Nat.d_div'45'helper_60
                                                                                    (addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v0))
                                                                                    v1 v12 v1))
                                                                              (d_acc'8804'div'8341''91'acc'93'_368
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (1 ::
                                                                                          Integer))
                                                                                    (coe v0))
                                                                                 (coe v1) (coe v12)
                                                                                 (coe v1)))
                                                                           (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                                                              (coe v0)))
                                                                        erased))
                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                          _ -> MAlonzo.RTE.mazUnreachableError)))))
      _ -> MAlonzo.RTE.mazUnreachableError
