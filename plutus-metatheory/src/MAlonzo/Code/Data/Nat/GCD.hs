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

module MAlonzo.Code.Data.Nat.GCD where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.GCD.Lemmas
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction
import qualified MAlonzo.Code.Induction.Lexicographic
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Double
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Nat.GCD.Algebra.Associative
d_Associative_30 :: (Integer -> Integer -> Integer) -> ()
d_Associative_30 = erased
-- Data.Nat.GCD.Algebra.Commutative
d_Commutative_34 :: (Integer -> Integer -> Integer) -> ()
d_Commutative_34 = erased
-- Data.Nat.GCD.Algebra.Identity
d_Identity_50 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Identity_50 = erased
-- Data.Nat.GCD.Algebra.LeftIdentity
d_LeftIdentity_76 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftIdentity_76 = erased
-- Data.Nat.GCD.Algebra.LeftZero
d_LeftZero_84 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftZero_84 = erased
-- Data.Nat.GCD.Algebra.RightIdentity
d_RightIdentity_106 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_RightIdentity_106 = erased
-- Data.Nat.GCD.Algebra.RightZero
d_RightZero_114 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_RightZero_114 = erased
-- Data.Nat.GCD.Algebra.Zero
d_Zero_134 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Zero_134 = erased
-- Data.Nat.GCD.gcd′
d_gcd'8242'_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_gcd'8242'_140 v0 v1 ~v2 ~v3 = du_gcd'8242'_140 v0 v1
du_gcd'8242'_140 :: Integer -> Integer -> Integer
du_gcd'8242'_140 v0 v1
  = case coe v1 of
      0 -> coe v0
      _ -> coe
             du_gcd'8242'_140 (coe v1)
             (coe MAlonzo.Code.Data.Nat.Base.du__'37'__326 (coe v0) (coe v1))
-- Data.Nat.GCD.gcd
d_gcd_152 :: Integer -> Integer -> Integer
d_gcd_152 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2700
                   (coe v0))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                 (coe eqInt (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                    (coe eqInt (coe v0) (coe v1)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe seq (coe v4) (coe v0)
                else (let v5
                            = seq
                                (coe v4)
                                (let v5 = ltInt (coe v0) (coe v1) in
                                 coe
                                   (if coe v5
                                      then coe
                                             seq
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                (coe v5))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2738
                                                   (coe v0)))
                                      else coe
                                             seq
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                (coe v5))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2974
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2958
                                                      (coe v0) (coe v1)))))) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v6
                             -> coe du_gcd'8242'_140 (coe v1) (coe v0)
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                             -> coe v0
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v8
                             -> coe du_gcd'8242'_140 (coe v0) (coe v1)
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.GCD.gcd′[m,n]∣m,n
d_gcd'8242''91'm'44'n'93''8739'm'44'n_186 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gcd'8242''91'm'44'n'93''8739'm'44'n_186 v0 v1 ~v2 ~v3
  = du_gcd'8242''91'm'44'n'93''8739'm'44'n_186 v0 v1
du_gcd'8242''91'm'44'n'93''8739'm'44'n_186 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_gcd'8242''91'm'44'n'93''8739'm'44'n_186 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166)
             (coe MAlonzo.Code.Data.Nat.Divisibility.du__'8739'0_282)
      _ -> let v2
                 = coe
                     du_gcd'8242''91'm'44'n'93''8739'm'44'n_186 (coe v1)
                     (coe remInt (coe v0) (coe v1)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Nat.Divisibility.du_'8739'n'8739'm'37'n'8658''8739'm_624
                          (coe du_gcd'8242'_140 (coe v1) (coe remInt (coe v0) (coe v1)))
                          (coe v0) (coe v3) (coe v4))
                       (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.GCD.gcd′-greatest
d_gcd'8242''45'greatest_220 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'8242''45'greatest_220 v0 v1 v2 ~v3 ~v4 v5 v6
  = du_gcd'8242''45'greatest_220 v0 v1 v2 v5 v6
du_gcd'8242''45'greatest_220 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_gcd'8242''45'greatest_220 v0 v1 v2 v3 v4
  = case coe v1 of
      0 -> coe v3
      _ -> coe
             du_gcd'8242''45'greatest_220 (coe v1)
             (coe remInt (coe v0) (coe v1)) (coe v2) (coe v4)
             (coe
                MAlonzo.Code.Data.Nat.Divisibility.du_'37''45'pres'737''45''8739'_648
                (coe v1) (coe v2) (coe v3) (coe v4))
-- Data.Nat.GCD.gcd[m,n]∣m
d_gcd'91'm'44'n'93''8739'm_248 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'm'44'n'93''8739'm_248 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2700
                   (coe v0))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                 (coe eqInt (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                    (coe eqInt (coe v0) (coe v1)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166)
                else (let v5
                            = seq
                                (coe v4)
                                (let v5 = ltInt (coe v0) (coe v1) in
                                 coe
                                   (if coe v5
                                      then coe
                                             seq
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                (coe v5))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2738
                                                   (coe v0)))
                                      else coe
                                             seq
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                (coe v5))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2974
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2958
                                                      (coe v0) (coe v1)))))) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe du_gcd'8242''91'm'44'n'93''8739'm'44'n_186 (coe v1) (coe v0))
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                             -> coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe du_gcd'8242''91'm'44'n'93''8739'm'44'n_186 (coe v0) (coe v1))
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.GCD.gcd[m,n]∣n
d_gcd'91'm'44'n'93''8739'n_278 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'm'44'n'93''8739'n_278 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2700
                   (coe v0))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                 (coe eqInt (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                    (coe eqInt (coe v0) (coe v1)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166)
                else (let v5
                            = seq
                                (coe v4)
                                (let v5 = ltInt (coe v0) (coe v1) in
                                 coe
                                   (if coe v5
                                      then coe
                                             seq
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                (coe v5))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2738
                                                   (coe v0)))
                                      else coe
                                             seq
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                (coe v5))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2974
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2958
                                                      (coe v0) (coe v1)))))) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe du_gcd'8242''91'm'44'n'93''8739'm'44'n_186 (coe v1) (coe v0))
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                             -> coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe du_gcd'8242''91'm'44'n'93''8739'm'44'n_186 (coe v0) (coe v1))
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.GCD.gcd-greatest
d_gcd'45'greatest_310 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'45'greatest_310 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v5 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2700
                   (coe v0))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                 (coe eqInt (coe v0) (coe v1))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                    (coe eqInt (coe v0) (coe v1)))) in
    coe
      (case coe v5 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
           -> if coe v6
                then coe seq (coe v7) (coe v3)
                else (let v8
                            = seq
                                (coe v7)
                                (let v8 = ltInt (coe v0) (coe v1) in
                                 coe
                                   (if coe v8
                                      then coe
                                             seq
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                (coe v8))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2738
                                                   (coe v0)))
                                      else coe
                                             seq
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                (coe v8))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2974
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2958
                                                      (coe v0) (coe v1)))))) in
                      coe
                        (case coe v8 of
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v9
                             -> coe
                                  du_gcd'8242''45'greatest_220 (coe v1) (coe v0) (coe v2) (coe v4)
                                  (coe v3)
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v10
                             -> coe v3
                           MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v11
                             -> coe
                                  du_gcd'8242''45'greatest_220 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.GCD.gcd[0,0]≡0
d_gcd'91'0'44'0'93''8801'0_352 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'91'0'44'0'93''8801'0_352 = erased
-- Data.Nat.GCD.gcd[m,n]≢0
d_gcd'91'm'44'n'93''8802'0_358 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_gcd'91'm'44'n'93''8802'0_358 = erased
-- Data.Nat.GCD.gcd[m,n]≡0⇒m≡0
d_gcd'91'm'44'n'93''8801'0'8658'm'8801'0_384 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'91'm'44'n'93''8801'0'8658'm'8801'0_384 = erased
-- Data.Nat.GCD.gcd[m,n]≡0⇒n≡0
d_gcd'91'm'44'n'93''8801'0'8658'n'8801'0_400 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'91'm'44'n'93''8801'0'8658'n'8801'0_400 = erased
-- Data.Nat.GCD.gcd-comm
d_gcd'45'comm_412 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'comm_412 = erased
-- Data.Nat.GCD.gcd-assoc
d_gcd'45'assoc_418 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'assoc_418 = erased
-- Data.Nat.GCD._.gcd[gcd[m,n],p]|m
d_gcd'91'gcd'91'm'44'n'93''44'p'93''124'm_430 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'gcd'91'm'44'n'93''44'p'93''124'm_430 v0 v1 v2
  = let v3
          = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'preorder_204 in
    coe
      (let v4
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
               (coe v4))
            (d_gcd_152 (coe d_gcd_152 (coe v0) (coe v1)) (coe v2)) v0
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe
                     MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
               (d_gcd_152 (coe d_gcd_152 (coe v0) (coe v1)) (coe v2))
               (d_gcd_152 (coe v0) (coe v1)) v0
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                     (coe
                        MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
                  (d_gcd_152 (coe v0) (coe v1)) v0 v0
                  (let v5
                         = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                           (coe v5))
                        (coe v0)))
                  (d_gcd'91'm'44'n'93''8739'm_248 (coe v0) (coe v1)))
               (d_gcd'91'm'44'n'93''8739'm_248
                  (coe d_gcd_152 (coe v0) (coe v1)) (coe v2)))))
-- Data.Nat.GCD._.gcd[gcd[m,n],p]∣n
d_gcd'91'gcd'91'm'44'n'93''44'p'93''8739'n_432 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'gcd'91'm'44'n'93''44'p'93''8739'n_432 v0 v1 v2
  = let v3
          = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'preorder_204 in
    coe
      (let v4
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
               (coe v4))
            (d_gcd_152 (coe d_gcd_152 (coe v0) (coe v1)) (coe v2)) v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe
                     MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
               (d_gcd_152 (coe d_gcd_152 (coe v0) (coe v1)) (coe v2))
               (d_gcd_152 (coe v0) (coe v1)) v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                     (coe
                        MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
                  (d_gcd_152 (coe v0) (coe v1)) v1 v1
                  (let v5
                         = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                           (coe v5))
                        (coe v1)))
                  (d_gcd'91'm'44'n'93''8739'n_278 (coe v0) (coe v1)))
               (d_gcd'91'm'44'n'93''8739'm_248
                  (coe d_gcd_152 (coe v0) (coe v1)) (coe v2)))))
-- Data.Nat.GCD._.gcd[gcd[m,n],p]∣p
d_gcd'91'gcd'91'm'44'n'93''44'p'93''8739'p_434 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'gcd'91'm'44'n'93''44'p'93''8739'p_434 v0 v1 v2
  = coe
      d_gcd'91'm'44'n'93''8739'n_278 (coe d_gcd_152 (coe v0) (coe v1))
      (coe v2)
-- Data.Nat.GCD._.gcd[m,gcd[n,p]]∣m
d_gcd'91'm'44'gcd'91'n'44'p'93''93''8739'm_436 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'm'44'gcd'91'n'44'p'93''93''8739'm_436 v0 v1 v2
  = coe
      d_gcd'91'm'44'n'93''8739'm_248 (coe v0)
      (coe d_gcd_152 (coe v1) (coe v2))
-- Data.Nat.GCD._.gcd[m,gcd[n,p]]∣n
d_gcd'91'm'44'gcd'91'n'44'p'93''93''8739'n_438 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'm'44'gcd'91'n'44'p'93''93''8739'n_438 v0 v1 v2
  = let v3
          = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'preorder_204 in
    coe
      (let v4
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
               (coe v4))
            (d_gcd_152 (coe v0) (coe d_gcd_152 (coe v1) (coe v2))) v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe
                     MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
               (d_gcd_152 (coe v0) (coe d_gcd_152 (coe v1) (coe v2)))
               (d_gcd_152 (coe v1) (coe v2)) v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                     (coe
                        MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
                  (d_gcd_152 (coe v1) (coe v2)) v1 v1
                  (let v5
                         = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                           (coe v5))
                        (coe v1)))
                  (d_gcd'91'm'44'n'93''8739'm_248 (coe v1) (coe v2)))
               (d_gcd'91'm'44'n'93''8739'n_278
                  (coe v0) (coe d_gcd_152 (coe v1) (coe v2))))))
-- Data.Nat.GCD._.gcd[m,gcd[n,p]]∣p
d_gcd'91'm'44'gcd'91'n'44'p'93''93''8739'p_440 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'm'44'gcd'91'n'44'p'93''93''8739'p_440 v0 v1 v2
  = let v3
          = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'preorder_204 in
    coe
      (let v4
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v3) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
               (coe v4))
            (d_gcd_152 (coe v0) (coe d_gcd_152 (coe v1) (coe v2))) v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe
                     MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
               (d_gcd_152 (coe v0) (coe d_gcd_152 (coe v1) (coe v2)))
               (d_gcd_152 (coe v1) (coe v2)) v2
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                     (coe
                        MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
                  (d_gcd_152 (coe v1) (coe v2)) v2 v2
                  (let v5
                         = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                           (coe v5))
                        (coe v2)))
                  (d_gcd'91'm'44'n'93''8739'n_278 (coe v1) (coe v2)))
               (d_gcd'91'm'44'n'93''8739'n_278
                  (coe v0) (coe d_gcd_152 (coe v1) (coe v2))))))
-- Data.Nat.GCD.gcd-identityˡ
d_gcd'45'identity'737'_442 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'identity'737'_442 = erased
-- Data.Nat.GCD.gcd-identityʳ
d_gcd'45'identity'691'_444 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'identity'691'_444 = erased
-- Data.Nat.GCD.gcd-identity
d_gcd'45'identity_446 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gcd'45'identity_446
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.GCD.gcd-zeroˡ
d_gcd'45'zero'737'_448 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'zero'737'_448 = erased
-- Data.Nat.GCD._.gcd[1,n]∣1
d_gcd'91'1'44'n'93''8739'1_456 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'1'44'n'93''8739'1_456 v0
  = coe d_gcd'91'm'44'n'93''8739'm_248 (coe (1 :: Integer)) (coe v0)
-- Data.Nat.GCD._.1∣gcd[1,n]
d_1'8739'gcd'91'1'44'n'93'_458 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_1'8739'gcd'91'1'44'n'93'_458 v0
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.d_1'8739'__294
      (coe d_gcd_152 (coe (1 :: Integer)) (coe v0))
-- Data.Nat.GCD.gcd-zeroʳ
d_gcd'45'zero'691'_460 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'zero'691'_460 = erased
-- Data.Nat.GCD._.gcd[n,1]∣1
d_gcd'91'n'44'1'93''8739'1_468 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'91'n'44'1'93''8739'1_468 v0
  = coe d_gcd'91'm'44'n'93''8739'n_278 (coe v0) (coe (1 :: Integer))
-- Data.Nat.GCD._.1∣gcd[n,1]
d_1'8739'gcd'91'n'44'1'93'_470 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_1'8739'gcd'91'n'44'1'93'_470 v0
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.d_1'8739'__294
      (coe d_gcd_152 (coe v0) (coe (1 :: Integer)))
-- Data.Nat.GCD.gcd-zero
d_gcd'45'zero_472 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gcd'45'zero_472
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.GCD.gcd-universality
d_gcd'45'universality_484 ::
  Integer ->
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'45'universality_484 = erased
-- Data.Nat.GCD.gcd[cm,cn]/c≡gcd[m,n]
d_gcd'91'cm'44'cn'93''47'c'8801'gcd'91'm'44'n'93'_510 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gcd'91'cm'44'cn'93''47'c'8801'gcd'91'm'44'n'93'_510 = erased
-- Data.Nat.GCD._.forwards
d_forwards_524 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_forwards_524 v0 v1 v2 ~v3 v4 v5 = du_forwards_524 v0 v1 v2 v4 v5
du_forwards_524 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_forwards_524 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> coe
             d_gcd'45'greatest_310 (coe mulInt (coe v0) (coe v1))
             (coe mulInt (coe v0) (coe v2)) (coe mulInt (coe v0) (coe v3))
             (coe
                MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'mono'691''45''8739'_426
                v5)
             (coe
                MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'mono'691''45''8739'_426
                v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD._.backwards
d_backwards_534 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_backwards_534 v0 v1 v2 ~v3 v4 v5
  = du_backwards_534 v0 v1 v2 v4 v5
du_backwards_534 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_backwards_534 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Data.Nat.Divisibility.du_m'8739'n'47'o'8658'm'42'o'8739'n_554
              (coe v0) (coe v3)
              (coe
                 d_gcd'45'greatest_310 (coe mulInt (coe v0) (coe v1))
                 (coe mulInt (coe v0) (coe v2)) (coe v0)
                 (coe
                    MAlonzo.Code.Data.Nat.Divisibility.du_m'8739'm'42'n_346 (coe v1))
                 (coe
                    MAlonzo.Code.Data.Nat.Divisibility.du_m'8739'm'42'n_346 (coe v2)))
              (coe v4) in
    coe
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'cancel'737''45''8739'_440
            (coe
               MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'trans_168 (coe v5)
               (coe
                  d_gcd'91'm'44'n'93''8739'm_248 (coe mulInt (coe v0) (coe v1))
                  (coe mulInt (coe v0) (coe v2)))))
         (coe
            MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'cancel'737''45''8739'_440
            (coe
               MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'trans_168 (coe v5)
               (coe
                  d_gcd'91'm'44'n'93''8739'n_278 (coe mulInt (coe v0) (coe v1))
                  (coe mulInt (coe v0) (coe v2))))))
-- Data.Nat.GCD.c*gcd[m,n]≡gcd[cm,cn]
d_c'42'gcd'91'm'44'n'93''8801'gcd'91'cm'44'cn'93'_552 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c'42'gcd'91'm'44'n'93''8801'gcd'91'cm'44'cn'93'_552 = erased
-- Data.Nat.GCD.gcd[m,n]≤n
d_gcd'91'm'44'n'93''8804'n_576 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_gcd'91'm'44'n'93''8804'n_576 v0 v1 ~v2
  = du_gcd'91'm'44'n'93''8804'n_576 v0 v1
du_gcd'91'm'44'n'93''8804'n_576 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_gcd'91'm'44'n'93''8804'n_576 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.du_'8739''8658''8804'_142
      (coe d_gcd_152 (coe v0) (coe v1))
      (coe d_gcd'91'm'44'n'93''8739'n_278 (coe v0) (coe v1))
-- Data.Nat.GCD.n/gcd[m,n]≢0
d_n'47'gcd'91'm'44'n'93''8802'0_590 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'47'gcd'91'm'44'n'93''8802'0_590 = erased
-- Data.Nat.GCD.m/gcd[m,n]≢0
d_m'47'gcd'91'm'44'n'93''8802'0_604 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'47'gcd'91'm'44'n'93''8802'0_604 = erased
-- Data.Nat.GCD.GCD.GCD
d_GCD_622 a0 a1 a2 = ()
data T_GCD_622
  = C_is_646 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
             (Integer ->
              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
              MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20)
-- Data.Nat.GCD.GCD.GCD.commonDivisor
d_commonDivisor_636 ::
  T_GCD_622 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_commonDivisor_636 v0
  = case coe v0 of
      C_is_646 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.GCD.GCD.greatest
d_greatest_640 ::
  T_GCD_622 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_greatest_640 v0
  = case coe v0 of
      C_is_646 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.GCD.GCD.gcd∣m
d_gcd'8739'm_642 ::
  Integer ->
  Integer ->
  Integer ->
  T_GCD_622 -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'8739'm_642 ~v0 ~v1 ~v2 v3 = du_gcd'8739'm_642 v3
du_gcd'8739'm_642 ::
  T_GCD_622 -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_gcd'8739'm_642 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_commonDivisor_636 (coe v0))
-- Data.Nat.GCD.GCD.GCD.gcd∣n
d_gcd'8739'n_644 ::
  Integer ->
  Integer ->
  Integer ->
  T_GCD_622 -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_gcd'8739'n_644 ~v0 ~v1 ~v2 v3 = du_gcd'8739'n_644 v3
du_gcd'8739'n_644 ::
  T_GCD_622 -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_gcd'8739'n_644 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_commonDivisor_636 (coe v0))
-- Data.Nat.GCD.GCD.unique
d_unique_656 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  T_GCD_622 ->
  T_GCD_622 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique_656 = erased
-- Data.Nat.GCD.GCD.sym
d_sym_668 ::
  Integer -> Integer -> Integer -> T_GCD_622 -> T_GCD_622
d_sym_668 ~v0 ~v1 ~v2 v3 = du_sym_668 v3
du_sym_668 :: T_GCD_622 -> T_GCD_622
du_sym_668 v0
  = coe
      C_is_646
      (coe
         MAlonzo.Code.Data.Product.Base.du_swap_370
         (coe d_commonDivisor_636 (coe v0)))
      (coe
         (\ v1 v2 ->
            coe
              d_greatest_640 v0 v1
              (coe MAlonzo.Code.Data.Product.Base.du_swap_370 (coe v2))))
-- Data.Nat.GCD.GCD.refl
d_refl_674 :: Integer -> T_GCD_622
d_refl_674 ~v0 = du_refl_674
du_refl_674 :: T_GCD_622
du_refl_674
  = coe
      C_is_646
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166)
         (coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166))
      (coe
         (\ v0 v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
-- Data.Nat.GCD.GCD.base
d_base_678 :: Integer -> T_GCD_622
d_base_678 ~v0 = du_base_678
du_base_678 :: T_GCD_622
du_base_678
  = coe
      C_is_646
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Data.Nat.Divisibility.du__'8739'0_282)
         (coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166))
      (coe
         (\ v0 v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
-- Data.Nat.GCD.GCD.step
d_step_688 ::
  Integer -> Integer -> Integer -> T_GCD_622 -> T_GCD_622
d_step_688 ~v0 ~v1 ~v2 v3 = du_step_688 v3
du_step_688 :: T_GCD_622 -> T_GCD_622
du_step_688 v0
  = let v1 = d_commonDivisor_636 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
           -> coe
                C_is_646
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Data.Nat.Divisibility.du_'8739'm'8739'n'8658''8739'm'43'n_306
                      (coe v2) (coe v3)))
                (coe du_greatest'8242'_708 (coe v0))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.GCD.GCD._.greatest′
d_greatest'8242'_708 ::
  Integer ->
  Integer ->
  Integer ->
  T_GCD_622 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_greatest'8242'_708 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_greatest'8242'_708 v3 v6 v7
du_greatest'8242'_708 ::
  T_GCD_622 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_greatest'8242'_708 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             d_greatest_640 v0 v1
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Data.Nat.Divisibility.du_'8739'm'43'n'8739'm'8658''8739'n_312
                   (coe v4) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.gcd-GCD
d_gcd'45'GCD_722 :: Integer -> Integer -> T_GCD_622
d_gcd'45'GCD_722 v0 v1
  = coe
      C_is_646
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_gcd'91'm'44'n'93''8739'm_248 (coe v0) (coe v1))
         (coe d_gcd'91'm'44'n'93''8739'n_278 (coe v0) (coe v1)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_uncurry'8242'_320
              (d_gcd'45'greatest_310 (coe v0) (coe v1) (coe v2))))
-- Data.Nat.GCD.mkGCD
d_mkGCD_734 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mkGCD_734 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_gcd_152 (coe v0) (coe v1))
      (coe d_gcd'45'GCD_722 (coe v0) (coe v1))
-- Data.Nat.GCD.gcd?
d_gcd'63'_746 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_gcd'63'_746 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (\ v3 -> coe du_'46'extendedlambda0_754 (coe v0) (coe v1)) erased
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710
         (coe d_gcd_152 (coe v0) (coe v1)) (coe v2))
-- Data.Nat.GCD..extendedlambda0
d_'46'extendedlambda0_754 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_GCD_622
d_'46'extendedlambda0_754 v0 v1 ~v2 ~v3
  = du_'46'extendedlambda0_754 v0 v1
du_'46'extendedlambda0_754 :: Integer -> Integer -> T_GCD_622
du_'46'extendedlambda0_754 v0 v1
  = coe d_gcd'45'GCD_722 (coe v0) (coe v1)
-- Data.Nat.GCD.GCD-*
d_GCD'45''42'_766 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_GCD_622 -> T_GCD_622
d_GCD'45''42'_766 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_GCD'45''42'_766 v3 v5
du_GCD'45''42'_766 :: Integer -> T_GCD_622 -> T_GCD_622
du_GCD'45''42'_766 v0 v1
  = case coe v1 of
      C_is_646 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    C_is_646
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'cancel'691''45''8739'_462
                          v4)
                       (coe
                          MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'cancel'691''45''8739'_462
                          v5))
                    (coe
                       (\ v6 v7 ->
                          coe
                            MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'cancel'691''45''8739'_462
                            (coe
                               v3 (mulInt (coe v6) (coe v0))
                               (coe
                                  MAlonzo.Code.Data.Product.Base.du_map_128
                                  (coe
                                     MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'mono'737''45''8739'_432)
                                  (coe
                                     (\ v8 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'mono'737''45''8739'_432))
                                  (coe v7)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.GCD-/
d_GCD'45''47'_786 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  T_GCD_622 -> T_GCD_622
d_GCD'45''47'_786 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8
  = du_GCD'45''47'_786 v3 v5 v6 v7 v8
du_GCD'45''47'_786 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  T_GCD_622 -> T_GCD_622
du_GCD'45''47'_786 v0 v1 v2 v3 v4
  = coe
      seq (coe v1)
      (coe
         seq (coe v2)
         (coe seq (coe v3) (coe du_GCD'45''42'_766 (coe v0) (coe v4))))
-- Data.Nat.GCD.GCD-/gcd
d_GCD'45''47'gcd_824 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_GCD_622
d_GCD'45''47'gcd_824 v0 v1 ~v2 = du_GCD'45''47'gcd_824 v0 v1
du_GCD'45''47'gcd_824 :: Integer -> Integer -> T_GCD_622
du_GCD'45''47'gcd_824 v0 v1
  = coe
      du_GCD'45''47'_786 (coe d_gcd_152 (coe v0) (coe v1))
      (coe d_gcd'91'm'44'n'93''8739'm_248 (coe v0) (coe v1))
      (coe d_gcd'91'm'44'n'93''8739'n_278 (coe v0) (coe v1))
      (coe MAlonzo.Code.Data.Nat.Divisibility.du_'8739''45'refl_166)
      (coe d_gcd'45'GCD_722 (coe v0) (coe v1))
-- Data.Nat.GCD.Bézout.Identity.Identity
d_Identity_844 a0 a1 a2 = ()
data T_Identity_844
  = C_'43''45'_858 Integer Integer | C_'45''43'_866 Integer Integer
-- Data.Nat.GCD.Bézout.Identity.sym
d_sym_870 ::
  Integer -> Integer -> Integer -> T_Identity_844 -> T_Identity_844
d_sym_870 ~v0 ~v1 ~v2 v3 = du_sym_870 v3
du_sym_870 :: T_Identity_844 -> T_Identity_844
du_sym_870 v0
  = case coe v0 of
      C_'43''45'_858 v1 v2 -> coe C_'45''43'_866 v2 v1
      C_'45''43'_866 v1 v2 -> coe C_'43''45'_858 v2 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.Bézout.Identity.refl
d_refl_886 :: Integer -> T_Identity_844
d_refl_886 ~v0 = du_refl_886
du_refl_886 :: T_Identity_844
du_refl_886 = coe C_'45''43'_866 (0 :: Integer) (1 :: Integer)
-- Data.Nat.GCD.Bézout.Identity.base
d_base_890 :: Integer -> T_Identity_844
d_base_890 ~v0 = du_base_890
du_base_890 :: T_Identity_844
du_base_890 = coe C_'45''43'_866 (0 :: Integer) (1 :: Integer)
-- Data.Nat.GCD.Bézout.Identity._⊕_
d__'8853'__892 :: Integer -> Integer -> Integer
d__'8853'__892 v0 v1
  = coe addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Nat.GCD.Bézout.Identity.step
d_step_904 ::
  Integer -> Integer -> Integer -> T_Identity_844 -> T_Identity_844
d_step_904 ~v0 ~v1 ~v2 v3 = du_step_904 v3
du_step_904 :: T_Identity_844 -> T_Identity_844
du_step_904 v0
  = case coe v0 of
      C_'43''45'_858 v1 v2
        -> let v4
                 = MAlonzo.Code.Data.Nat.Base.d_compare_470 (coe v1) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Data.Nat.Base.C_less_454 v6
                  -> coe
                       C_'43''45'_858
                       (d__'8853'__892
                          (coe mulInt (coe (2 :: Integer)) (coe v1)) (coe v6))
                       (d__'8853'__892 (coe v1) (coe v6))
                MAlonzo.Code.Data.Nat.Base.C_equal_458
                  -> coe C_'43''45'_858 (mulInt (coe (2 :: Integer)) (coe v1)) v1
                MAlonzo.Code.Data.Nat.Base.C_greater_464 v6
                  -> coe
                       C_'43''45'_858
                       (d__'8853'__892
                          (coe mulInt (coe (2 :: Integer)) (coe v2)) (coe v6))
                       v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_'45''43'_866 v1 v2
        -> let v4
                 = MAlonzo.Code.Data.Nat.Base.d_compare_470 (coe v1) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Data.Nat.Base.C_less_454 v6
                  -> coe
                       C_'45''43'_866
                       (d__'8853'__892
                          (coe mulInt (coe (2 :: Integer)) (coe v1)) (coe v6))
                       (d__'8853'__892 (coe v1) (coe v6))
                MAlonzo.Code.Data.Nat.Base.C_equal_458
                  -> coe C_'45''43'_866 (mulInt (coe (2 :: Integer)) (coe v1)) v1
                MAlonzo.Code.Data.Nat.Base.C_greater_464 v6
                  -> coe
                       C_'45''43'_866
                       (d__'8853'__892
                          (coe mulInt (coe (2 :: Integer)) (coe v2)) (coe v6))
                       v2
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.Bézout.Lemma.Lemma
d_Lemma_1020 a0 a1 = ()
data T_Lemma_1020 = C_result_1032 Integer T_GCD_622 T_Identity_844
-- Data.Nat.GCD.Bézout.Lemma.sym
d_sym_1034 :: Integer -> Integer -> T_Lemma_1020 -> T_Lemma_1020
d_sym_1034 ~v0 ~v1 v2 = du_sym_1034 v2
du_sym_1034 :: T_Lemma_1020 -> T_Lemma_1020
du_sym_1034 v0
  = case coe v0 of
      C_result_1032 v1 v2 v3
        -> coe
             C_result_1032 (coe v1) (coe du_sym_668 (coe v2))
             (coe du_sym_870 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.Bézout.Lemma.base
d_base_1044 :: Integer -> T_Lemma_1020
d_base_1044 v0
  = coe C_result_1032 (coe v0) (coe du_base_678) (coe du_base_890)
-- Data.Nat.GCD.Bézout.Lemma.refl
d_refl_1050 :: Integer -> T_Lemma_1020
d_refl_1050 v0
  = coe C_result_1032 (coe v0) (coe du_refl_674) (coe du_refl_886)
-- Data.Nat.GCD.Bézout.Lemma.stepˡ
d_step'737'_1058 ::
  Integer -> Integer -> T_Lemma_1020 -> T_Lemma_1020
d_step'737'_1058 ~v0 ~v1 v2 = du_step'737'_1058 v2
du_step'737'_1058 :: T_Lemma_1020 -> T_Lemma_1020
du_step'737'_1058 v0
  = case coe v0 of
      C_result_1032 v1 v2 v3
        -> coe
             C_result_1032 (coe v1) (coe du_step_688 (coe v2))
             (coe du_step_904 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.Bézout.Lemma.stepʳ
d_step'691'_1074 ::
  Integer -> Integer -> T_Lemma_1020 -> T_Lemma_1020
d_step'691'_1074 ~v0 ~v1 v2 = du_step'691'_1074 v2
du_step'691'_1074 :: T_Lemma_1020 -> T_Lemma_1020
du_step'691'_1074 v0
  = coe
      du_sym_1034 (coe du_step'737'_1058 (coe du_sym_1034 (coe v0)))
-- Data.Nat.GCD.Bézout.lemma
d_lemma_1080 :: Integer -> Integer -> T_Lemma_1020
d_lemma_1080 v0 v1
  = coe
      MAlonzo.Code.Induction.du_build_36
      (coe
         MAlonzo.Code.Induction.Lexicographic.du_'91'_'8855'_'93'_166
         (\ v2 v3 v4 v5 ->
            coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v3 v5)
         (\ v2 v3 v4 v5 ->
            coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v3 v5))
      erased (coe du_gcd'8243'_1098)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
-- Data.Nat.GCD.Bézout._.P
d_P_1090 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_P_1090 = erased
-- Data.Nat.GCD.Bézout._.gcd″
d_gcd'8243'_1098 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Lemma_1020
d_gcd'8243'_1098 ~v0 ~v1 v2 v3 = du_gcd'8243'_1098 v2 v3
du_gcd'8243'_1098 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Lemma_1020
du_gcd'8243'_1098 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             0 -> coe d_base_1044 (coe v3)
             _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (case coe v3 of
                       0 -> coe du_sym_1034 (coe d_base_1044 (coe v2))
                       _ -> let v5 = subInt (coe v3) (coe (1 :: Integer)) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Data.Nat.Base.d_compare_470 (coe v4) (coe v5) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Data.Nat.Base.C_less_454 v8
                                      -> coe
                                           du_step'737'_1058
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v1
                                              (addInt (coe (1 :: Integer)) (coe v8))
                                              (MAlonzo.Code.Data.Nat.GCD.Lemmas.d_lem'8321'_70
                                                 (coe v8) (coe v4)))
                                    MAlonzo.Code.Data.Nat.Base.C_equal_458
                                      -> coe d_refl_1050 (coe v2)
                                    MAlonzo.Code.Data.Nat.Base.C_greater_464 v8
                                      -> coe
                                           du_step'691'_1074
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1
                                              (addInt (coe (1 :: Integer)) (coe v8))
                                              (MAlonzo.Code.Data.Nat.GCD.Lemmas.d_lem'8321'_70
                                                 (coe v8) (coe v5))
                                              v3)
                                    _ -> MAlonzo.RTE.mazUnreachableError)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.GCD.Bézout.identity
d_identity_1168 ::
  Integer -> Integer -> Integer -> T_GCD_622 -> T_Identity_844
d_identity_1168 v0 v1 ~v2 ~v3 = du_identity_1168 v0 v1
du_identity_1168 :: Integer -> Integer -> T_Identity_844
du_identity_1168 v0 v1
  = let v2
          = coe
              du_gcd'8243'_1098
              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
              (coe
                 MAlonzo.Code.Induction.Lexicographic.du_'91'_'8855'_'93'_166
                 (\ v2 v3 v4 v5 ->
                    coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v3 v5)
                 (\ v2 v3 v4 v5 ->
                    coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v3 v5)
                 erased (coe du_gcd'8243'_1098)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))) in
    coe
      (case coe v2 of
         C_result_1032 v3 v4 v5 -> coe v5
         _ -> MAlonzo.RTE.mazUnreachableError)
