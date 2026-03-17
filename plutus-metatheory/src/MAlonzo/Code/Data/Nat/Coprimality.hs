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

module MAlonzo.Code.Data.Nat.Coprimality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.GCD
import qualified MAlonzo.Code.Data.Nat.Primality
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Induction.Lexicographic
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Nat.Coprimality.Coprime
d_Coprime_16 :: Integer -> Integer -> ()
d_Coprime_16 = erased
-- Data.Nat.Coprimality.coprime⇒GCD≡1
d_coprime'8658'GCD'8801'1_24 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.GCD.T_GCD_622
d_coprime'8658'GCD'8801'1_24 v0 v1 ~v2
  = du_coprime'8658'GCD'8801'1_24 v0 v1
du_coprime'8658'GCD'8801'1_24 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.GCD.T_GCD_622
du_coprime'8658'GCD'8801'1_24 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.C_is_646
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Data.Nat.Divisibility.d_1'8739'__294 (coe v0))
         (coe MAlonzo.Code.Data.Nat.Divisibility.d_1'8739'__294 (coe v1)))
      (coe
         (\ v2 v3 ->
            coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'reflexive_162))
-- Data.Nat.Coprimality.GCD≡1⇒coprime
d_GCD'8801'1'8658'coprime_32 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.GCD.T_GCD_622 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_GCD'8801'1'8658'coprime_32 = erased
-- Data.Nat.Coprimality.coprime⇒gcd≡1
d_coprime'8658'gcd'8801'1_46 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coprime'8658'gcd'8801'1_46 = erased
-- Data.Nat.Coprimality.gcd≡1⇒coprime
d_gcd'8801'1'8658'coprime_50 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'8801'1'8658'coprime_50 = erased
-- Data.Nat.Coprimality.coprime-/gcd
d_coprime'45''47'gcd_60 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coprime'45''47'gcd_60 = erased
-- Data.Nat.Coprimality.sym
d_sym_66 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_66 = erased
-- Data.Nat.Coprimality.coprime?
d_coprime'63'_70 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_coprime'63'_70 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      erased erased
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710
         (coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1))
         (coe (1 :: Integer)))
-- Data.Nat.Coprimality.1-coprimeTo
d_1'45'coprimeTo_78 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'45'coprimeTo_78 = erased
-- Data.Nat.Coprimality.0-coprimeTo-m⇒m≡1
d_0'45'coprimeTo'45'm'8658'm'8801'1_82 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'45'coprimeTo'45'm'8658'm'8801'1_82 = erased
-- Data.Nat.Coprimality.¬0-coprimeTo-2+
d_'172'0'45'coprimeTo'45'2'43'_88 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'0'45'coprimeTo'45'2'43'_88 = erased
-- Data.Nat.Coprimality.coprime-+
d_coprime'45''43'_94 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coprime'45''43'_94 = erased
-- Data.Nat.Coprimality.recompute
d_recompute_102 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_recompute_102 = erased
-- Data.Nat.Coprimality.Bézout-coprime
d_Bézout'45'coprime_110 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.GCD.T_Identity_844 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Bézout'45'coprime_110 = erased
-- Data.Nat.Coprimality.coprime-Bézout
d_coprime'45'Bézout_132 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.GCD.T_Identity_844
d_coprime'45'Bézout_132 v0 v1 ~v2 = du_coprime'45'Bézout_132 v0 v1
du_coprime'45'Bézout_132 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.GCD.T_Identity_844
du_coprime'45'Bézout_132 v0 v1
  = coe MAlonzo.Code.Data.Nat.GCD.du_identity_1168 (coe v0) (coe v1)
-- Data.Nat.Coprimality.coprime-divisor
d_coprime'45'divisor_134 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_coprime'45'divisor_134 v0 v1 v2 ~v3 v4
  = du_coprime'45'divisor_134 v0 v1 v2 v4
du_coprime'45'divisor_134 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_coprime'45'divisor_134 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
        -> let v6
                 = coe
                     MAlonzo.Code.Data.Nat.GCD.du_gcd'8243'_1098
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
                     (coe
                        MAlonzo.Code.Induction.Lexicographic.du_'91'_'8855'_'93'_166
                        (\ v6 v7 v8 v9 ->
                           coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v7 v9)
                        (\ v6 v7 v8 v9 ->
                           coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v7 v9)
                        erased (coe MAlonzo.Code.Data.Nat.GCD.du_gcd'8243'_1098)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))) in
           coe
             (case coe v6 of
                MAlonzo.Code.Data.Nat.GCD.C_result_1032 v7 v8 v9
                  -> case coe v9 of
                       MAlonzo.Code.Data.Nat.GCD.C_'43''45'_858 v10 v11
                         -> coe
                              MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                 (mulInt (coe v10) (coe v2)) (mulInt (coe v11) (coe v4)))
                       MAlonzo.Code.Data.Nat.GCD.C_'45''43'_866 v10 v11
                         -> coe
                              MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                 (mulInt (coe v11) (coe v4)) (mulInt (coe v10) (coe v2)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Coprimality.coprime-factors
d_coprime'45'factors_176 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_coprime'45'factors_176 v0 v1 ~v2 ~v3 ~v4 v5
  = du_coprime'45'factors_176 v0 v1 v5
du_coprime'45'factors_176 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_coprime'45'factors_176 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v5
               -> case coe v4 of
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v7
                      -> let v9
                               = coe
                                   MAlonzo.Code.Data.Nat.GCD.du_gcd'8243'_1098
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
                                   (coe
                                      MAlonzo.Code.Induction.Lexicographic.du_'91'_'8855'_'93'_166
                                      (\ v9 v10 v11 v12 ->
                                         coe
                                           MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160
                                           v10 v12)
                                      (\ v9 v10 v11 v12 ->
                                         coe
                                           MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160
                                           v10 v12)
                                      erased (coe MAlonzo.Code.Data.Nat.GCD.du_gcd'8243'_1098)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                                         (coe v1))) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Data.Nat.GCD.C_result_1032 v10 v11 v12
                                -> case coe v12 of
                                     MAlonzo.Code.Data.Nat.GCD.C_'43''45'_858 v13 v14
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                               (mulInt (coe v13) (coe v5))
                                               (mulInt (coe v14) (coe v7)))
                                     MAlonzo.Code.Data.Nat.GCD.C_'45''43'_866 v13 v14
                                       -> coe
                                            MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                               (mulInt (coe v14) (coe v7))
                                               (mulInt (coe v13) (coe v5)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Coprimality.prime⇒coprime
d_prime'8658'coprime_224 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Primality.T_Prime_42 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prime'8658'coprime_224 = erased
