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

module MAlonzo.Code.Data.Integer.DivMod where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax

-- Data.Integer.DivMod.n%ℕd<d
d_n'37'ℕd'60'd_12 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'37'ℕd'60'd_12 v0 v1 ~v2 = du_n'37'ℕd'60'd_12 v0 v1
du_n'37'ℕd'60'd_12 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'37'ℕd'60'd_12 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Nat.DivMod.du_m'37'n'60'n_166 (coe v0) (coe v1)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v3
                    = subInt (coe (0 :: Integer)) (coe remInt (coe v0) (coe v1)) in
              coe
                (case coe v3 of
                   0 -> coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                   _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
                        coe
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                             (MAlonzo.Code.Data.Nat.Properties.d_m'8760'n'8804'm_5184
                                (coe v2) (coe v4)))))
-- Data.Integer.DivMod.n%d<d
d_n'37'd'60'd_42 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'37'd'60'd_42 v0 v1 ~v2 = du_n'37'd'60'd_42 v0 v1
du_n'37'd'60'd_42 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'37'd'60'd_42 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe du_n'37'ℕd'60'd_12 (coe v0) (coe v1)
      _ -> coe
             du_n'37'ℕd'60'd_12 (coe v0)
             (coe subInt (coe (0 :: Integer)) (coe v1))
-- Data.Integer.DivMod.a≡a%ℕn+[a/ℕn]*n
d_a'8801'a'37'ℕn'43''91'a'47'ℕn'93''42'n_58 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'8801'a'37'ℕn'43''91'a'47'ℕn'93''42'n_58 = erased
-- Data.Integer.DivMod._.∣n∣
d_'8739'n'8739'_86 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8739'n'8739'_86 v0 ~v1 ~v2 ~v3 = du_'8739'n'8739'_86 v0
du_'8739'n'8739'_86 :: Integer -> Integer
du_'8739'n'8739'_86 v0
  = coe
      MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
      (coe subInt (coe (-1 :: Integer)) (coe v0))
-- Data.Integer.DivMod._.q
d_q_88 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_q_88 v0 v1 ~v2 ~v3 = du_q_88 v0 v1
du_q_88 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
du_q_88 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'47'__318
      (coe du_'8739'n'8739'_86 (coe v0)) (coe v1)
-- Data.Integer.DivMod._.r
d_r_90 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_r_90 v0 v1 ~v2 ~v3 = du_r_90 v0 v1
du_r_90 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
du_r_90 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'37'__330
      (coe du_'8739'n'8739'_86 (coe v0)) (coe v1)
-- Data.Integer.DivMod.[n/ℕd]*d≤n
d_'91'n'47'ℕd'93''42'd'8804'n_126 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'91'n'47'ℕd'93''42'd'8804'n_126 v0 v1 ~v2
  = du_'91'n'47'ℕd'93''42'd'8804'n_126 v0 v1
du_'91'n'47'ℕd'93''42'd'8804'n_126 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'91'n'47'ℕd'93''42'd'8804'n_126 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe
            MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908)
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2954 v4))
      (MAlonzo.Code.Data.Integer.Base.d__'42'__316
         (coe
            MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1))
         (coe v1))
      v0
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe
               MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908)
            (\ v2 v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_3066
                 v5 v6))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__316
            (coe
               MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1))
            (coe v1))
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284
            (coe
               MAlonzo.Code.Data.Integer.Base.du__'37'ℕ__414 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe
                  MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1))
               (coe v1)))
         v0
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
            (\ v2 v3 v4 v5 v6 -> v6)
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284
               (coe
                  MAlonzo.Code.Data.Integer.Base.du__'37'ℕ__414 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe
                     MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1))
                  (coe v1)))
            v0 v0
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe
                     MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908))
               (coe v0))
            erased)
         (coe
            MAlonzo.Code.Data.Integer.Properties.du_i'8804'j'43'i_4668
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe
                  MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1))
               (coe v1))
            (coe
               MAlonzo.Code.Data.Integer.Base.du__'37'ℕ__414 (coe v0) (coe v1))))
-- Data.Integer.DivMod.div-pos-is-/ℕ
d_div'45'pos'45'is'45''47'ℕ_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_div'45'pos'45'is'45''47'ℕ_142 = erased
-- Data.Integer.DivMod.div-neg-is-neg-/ℕ
d_div'45'neg'45'is'45'neg'45''47'ℕ_156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_div'45'neg'45'is'45'neg'45''47'ℕ_156 = erased
-- Data.Integer.DivMod.0≤n⇒0≤n/ℕd
d_0'8804'n'8658'0'8804'n'47'ℕd_168 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_0'8804'n'8658'0'8804'n'47'ℕd_168 ~v0 ~v1 ~v2 v3
  = du_0'8804'n'8658'0'8804'n'47'ℕd_168 v3
du_0'8804'n'8658'0'8804'n'47'ℕd_168 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_0'8804'n'8658'0'8804'n'47'ℕd_168 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Data.Integer.DivMod.0≤n⇒0≤n/d
d_0'8804'n'8658'0'8804'n'47'd_182 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_0'8804'n'8658'0'8804'n'47'd_182 ~v0 ~v1 ~v2 v3 v4
  = du_0'8804'n'8658'0'8804'n'47'd_182 v3 v4
du_0'8804'n'8658'0'8804'n'47'd_182 ::
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_0'8804'n'8658'0'8804'n'47'd_182 v0 v1
  = coe
      seq (coe v1) (coe du_0'8804'n'8658'0'8804'n'47'ℕd_168 (coe v0))
-- Data.Integer.DivMod.[n/d]*d≤n
d_'91'n'47'd'93''42'd'8804'n_204 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'91'n'47'd'93''42'd'8804'n_204 v0 v1 ~v2
  = du_'91'n'47'd'93''42'd'8804'n_204 v0 v1
du_'91'n'47'd'93''42'd'8804'n_204 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'91'n'47'd'93''42'd'8804'n_204 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe
                  MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908)
               (\ v2 v3 v4 ->
                  coe
                    MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2954 v4))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe
                  MAlonzo.Code.Data.Integer.Base.du__'47'__402 (coe v0) (coe v1))
               (coe v1))
            v0
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe
                     MAlonzo.Code.Data.Integer.Base.du__'47'__402 (coe v0) (coe v1))
                  (coe v1))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe
                     MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1))
                  (coe v1))
               v0
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                     (coe
                        MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908)
                     (\ v2 v3 v4 v5 v6 ->
                        coe
                          MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_3066
                          v5 v6))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                     (coe
                        MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1))
                     (coe v1))
                  v0 v0
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe
                           MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908))
                     (coe v0))
                  (coe du_'91'n'47'ℕd'93''42'd'8804'n_126 (coe v0) (coe v1)))
               erased)
      _ -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                (coe
                   MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908)
                (\ v2 v3 v4 ->
                   coe
                     MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2954 v4))
             (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                (coe
                   MAlonzo.Code.Data.Integer.Base.du__'47'__402 (coe v0) (coe v1))
                (coe v1))
             v0
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                (\ v2 v3 v4 v5 v6 -> v6)
                (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                   (coe
                      MAlonzo.Code.Data.Integer.Base.du__'47'__402 (coe v0) (coe v1))
                   (coe v1))
                (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d_'45'__260
                      (coe
                         MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0)
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))))
                   (coe v1))
                v0
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                   (\ v2 v3 v4 v5 v6 -> v6)
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d_'45'__260
                         (coe
                            MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0)
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))))
                      (coe v1))
                   (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                      (coe
                         MAlonzo.Code.Data.Integer.Base.d__'42'__316
                         (coe
                            MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0)
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                         (coe v1)))
                   v0
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                      (\ v2 v3 v4 v5 v6 -> v6)
                      (MAlonzo.Code.Data.Integer.Base.d_'45'__260
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'42'__316
                            (coe
                               MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0)
                               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                            (coe v1)))
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                         (coe
                            MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0)
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                         (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                      v0
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe
                               MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908)
                            (\ v2 v3 v4 v5 v6 ->
                               coe
                                 MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_3066
                                 v5 v6))
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                            (coe
                               MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0)
                               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
                         v0 v0
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe
                                  MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908))
                            (coe v0))
                         (coe
                            du_'91'n'47'ℕd'93''42'd'8804'n_126 (coe v0)
                            (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))))
                      erased)
                   erased)
                erased)
-- Data.Integer.DivMod.n<s[n/ℕd]*d
d_n'60's'91'n'47'ℕd'93''42'd_226 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_n'60's'91'n'47'ℕd'93''42'd_226 v0 v1 ~v2
  = du_n'60's'91'n'47'ℕd'93''42'd_226 v0 v1
du_n'60's'91'n'47'ℕd'93''42'd_226 ::
  Integer -> Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_n'60's'91'n'47'ℕd'93''42'd_226 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
      (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__316
         (coe
            MAlonzo.Code.Data.Integer.Base.d_suc_308
            (coe
               MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1)))
         (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
         (\ v2 v3 v4 v5 v6 -> v6) v0
         (MAlonzo.Code.Data.Integer.Base.d__'43'__284
            (coe du_r_238 v0 v1 erased)
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe du_q_236 v0 v1 erased) (coe v1)))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__316
            (coe
               MAlonzo.Code.Data.Integer.Base.d_suc_308
               (coe
                  MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1)))
            (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (\ v2 v3 v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3094 v5 v6)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (\ v2 v3 v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_3080
                    v5 v6))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284
               (coe du_r_238 v0 v1 erased)
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe du_q_236 v0 v1 erased) (coe v1)))
            (MAlonzo.Code.Data.Integer.Base.d__'43'__284
               (coe v1)
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe du_q_236 v0 v1 erased) (coe v1)))
            (MAlonzo.Code.Data.Integer.Base.d__'42'__316
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_suc_308
                  (coe
                     MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1)))
               (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
               (\ v2 v3 v4 v5 v6 -> v6)
               (MAlonzo.Code.Data.Integer.Base.d__'43'__284
                  (coe v1)
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__316
                     (coe du_q_236 v0 v1 erased) (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d_suc_308
                     (coe
                        MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1)))
                  (coe v1))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d_suc_308
                     (coe
                        MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1)))
                  (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe
                        MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2908))
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__316
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d_suc_308
                        (coe
                           MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1)))
                     (coe v1)))
               erased)
            (coe
               MAlonzo.Code.Data.Integer.Properties.d_'43''45'mono'737''45''60'_4714
               (MAlonzo.Code.Data.Integer.Base.d__'42'__316
                  (coe du_q_236 v0 v1 erased) (coe v1))
               (coe
                  MAlonzo.Code.Data.Integer.Base.du__'37'ℕ__414 (coe v0) (coe v1))
               v1
               (coe
                  MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
                  (coe du_n'37'ℕd'60'd_12 (coe v0) (coe v1)))))
         erased)
-- Data.Integer.DivMod._.q
d_q_236 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_q_236 v0 v1 ~v2 = du_q_236 v0 v1
du_q_236 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
du_q_236 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 (coe v0) (coe v1)
-- Data.Integer.DivMod._.r
d_r_238 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_r_238 v0 v1 ~v2 = du_r_238 v0 v1
du_r_238 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
du_r_238 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.du__'37'ℕ__414 (coe v0) (coe v1)
-- Data.Integer.DivMod.a≡a%n+[a/n]*n
d_a'8801'a'37'n'43''91'a'47'n'93''42'n_246 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_a'8801'a'37'n'43''91'a'47'n'93''42'n_246 = erased
-- Data.Integer.DivMod._divℕ_
d__divℕ__272 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__divℕ__272 v0 v1 v2
  = coe MAlonzo.Code.Data.Integer.Base.du__'47'ℕ__372 v0 v1
-- Data.Integer.DivMod._div_
d__div__274 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__div__274 v0 v1 v2
  = coe MAlonzo.Code.Data.Integer.Base.du__'47'__402 v0 v1
-- Data.Integer.DivMod._modℕ_
d__modℕ__276 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__modℕ__276 v0 v1 v2
  = coe MAlonzo.Code.Data.Integer.Base.du__'37'ℕ__414 v0 v1
-- Data.Integer.DivMod._mod_
d__mod__278 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__mod__278 v0 v1 v2
  = coe MAlonzo.Code.Data.Integer.Base.du__'37'__444 v0 v1
