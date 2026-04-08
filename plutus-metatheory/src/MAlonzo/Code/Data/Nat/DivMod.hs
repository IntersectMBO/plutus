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

module MAlonzo.Code.Data.Nat.DivMod where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod.Core
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Nat.DivMod.m≡m%n+[m/n]*n
d_m'8801'm'37'n'43''91'm'47'n'93''42'n_20 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8801'm'37'n'43''91'm'47'n'93''42'n_20 = erased
-- Data.Nat.DivMod.m%n≡m∸m/n*n
d_m'37'n'8801'm'8760'm'47'n'42'n_32 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'37'n'8801'm'8760'm'47'n'42'n_32 = erased
-- Data.Nat.DivMod._.m/n*n
d_m'47'n'42'n_42 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_m'47'n'42'n_42 v0 v1 ~v2 = du_m'47'n'42'n_42 v0 v1
du_m'47'n'42'n_42 :: Integer -> Integer -> Integer
du_m'47'n'42'n_42 v0 v1
  = coe
      mulInt
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe v1)
-- Data.Nat.DivMod.%-congˡ
d_'37''45'cong'737'_48 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''45'cong'737'_48 = erased
-- Data.Nat.DivMod.%-congʳ
d_'37''45'cong'691'_54 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''45'cong'691'_54 = erased
-- Data.Nat.DivMod.n%1≡0
d_n'37'1'8801'0_58 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'37'1'8801'0_58 = erased
-- Data.Nat.DivMod.n%n≡0
d_n'37'n'8801'0_64 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'37'n'8801'0_64 = erased
-- Data.Nat.DivMod.m%n%n≡m%n
d_m'37'n'37'n'8801'm'37'n_74 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'37'n'37'n'8801'm'37'n_74 = erased
-- Data.Nat.DivMod.[m+n]%n≡m%n
d_'91'm'43'n'93''37'n'8801'm'37'n_86 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'43'n'93''37'n'8801'm'37'n_86 = erased
-- Data.Nat.DivMod.[m+kn]%n≡m%n
d_'91'm'43'kn'93''37'n'8801'm'37'n_100 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'43'kn'93''37'n'8801'm'37'n_100 = erased
-- Data.Nat.DivMod.m≤n⇒[n∸m]%m≡n%m
d_m'8804'n'8658''91'n'8760'm'93''37'm'8801'n'37'm_118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658''91'n'8760'm'93''37'm'8801'n'37'm_118 = erased
-- Data.Nat.DivMod.m*n≤o⇒[o∸m*n]%n≡o%n
d_m'42'n'8804'o'8658''91'o'8760'm'42'n'93''37'n'8801'o'37'n_136 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'8804'o'8658''91'o'8760'm'42'n'93''37'n'8801'o'37'n_136
  = erased
-- Data.Nat.DivMod.m*n%n≡0
d_m'42'n'37'n'8801'0_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'37'n'8801'0_154 = erased
-- Data.Nat.DivMod.m%n<n
d_m'37'n'60'n_166 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'37'n'60'n_166 v0 v1 ~v2 = du_m'37'n'60'n_166 v0 v1
du_m'37'n'60'n_166 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'37'n'60'n_166 v0 v1
  = let v2 = subInt (coe v1) (coe (1 :: Integer)) in
    coe
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (MAlonzo.Code.Data.Nat.DivMod.Core.d_a'91'mod'8341''93'n'60'n_70
            (coe (0 :: Integer)) (coe v0) (coe v2)))
-- Data.Nat.DivMod.m%n≤n
d_m'37'n'8804'n_178 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'37'n'8804'n_178 v0 v1 ~v2 = du_m'37'n'8804'n_178 v0 v1
du_m'37'n'8804'n_178 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'37'n'8804'n_178 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
      (coe du_m'37'n'60'n_166 (coe v0) (coe v1))
-- Data.Nat.DivMod.m%n≤m
d_m'37'n'8804'm_190 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'37'n'8804'm_190 v0 v1 ~v2 = du_m'37'n'8804'm_190 v0 v1
du_m'37'n'8804'm_190 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'37'n'8804'm_190 v0 v1
  = let v2 = subInt (coe v1) (coe (1 :: Integer)) in
    coe
      (coe
         MAlonzo.Code.Data.Nat.DivMod.Core.d_a'91'mod'8341''93'n'8804'a_96
         (coe (0 :: Integer)) (coe v0) (coe v2))
-- Data.Nat.DivMod.m≤n⇒m%n≡m
d_m'8804'n'8658'm'37'n'8801'm_196 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'37'n'8801'm_196 = erased
-- Data.Nat.DivMod.m<n⇒m%n≡m
d_m'60'n'8658'm'37'n'8801'm_210 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'60'n'8658'm'37'n'8801'm_210 = erased
-- Data.Nat.DivMod.%-pred-≡0
d_'37''45'pred'45''8801'0_220 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''45'pred'45''8801'0_220 = erased
-- Data.Nat.DivMod.m<[1+n%d]⇒m≤[n%d]
d_m'60''91'1'43'n'37'd'93''8658'm'8804''91'n'37'd'93'_236 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60''91'1'43'n'37'd'93''8658'm'8804''91'n'37'd'93'_236 ~v0 v1 v2
                                                          ~v3
  = du_m'60''91'1'43'n'37'd'93''8658'm'8804''91'n'37'd'93'_236 v1 v2
du_m'60''91'1'43'n'37'd'93''8658'm'8804''91'n'37'd'93'_236 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60''91'1'43'n'37'd'93''8658'm'8804''91'n'37'd'93'_236 v0 v1
  = case coe v1 of
      0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.DivMod.Core.du_k'60'1'43'a'91'mod'8341''93'n'8658'k'8804'a'91'mod'8341''93'n_216
                (coe (0 :: Integer)) (coe v0) (coe v2))
-- Data.Nat.DivMod.[1+m%d]≤1+n⇒[m%d]≤n
d_'91'1'43'm'37'd'93''8804'1'43'n'8658''91'm'37'd'93''8804'n_252 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'91'1'43'm'37'd'93''8804'1'43'n'8658''91'm'37'd'93''8804'n_252 v0
                                                                 ~v1 v2 ~v3 ~v4
  = du_'91'1'43'm'37'd'93''8804'1'43'n'8658''91'm'37'd'93''8804'n_252
      v0 v2
du_'91'1'43'm'37'd'93''8804'1'43'n'8658''91'm'37'd'93''8804'n_252 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'91'1'43'm'37'd'93''8804'1'43'n'8658''91'm'37'd'93''8804'n_252 v0
                                                                  v1
  = case coe v1 of
      0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.DivMod.Core.du_1'43'a'91'mod'8341''93'n'8804'1'43'k'8658'a'91'mod'8341''93'n'8804'k_260
                (coe (0 :: Integer)) (coe v0) (coe v2))
-- Data.Nat.DivMod.%-distribˡ-+
d_'37''45'distrib'737''45''43'_270 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''45'distrib'737''45''43'_270 = erased
-- Data.Nat.DivMod.%-distribˡ-*
d_'37''45'distrib'737''45''42'_300 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''45'distrib'737''45''42'_300 = erased
-- Data.Nat.DivMod._.m′
d_m'8242'_312 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_m'8242'_312 v0 ~v1 v2 ~v3 = du_m'8242'_312 v0 v2
du_m'8242'_312 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
du_m'8242'_312 v0 v1 v2
  = coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1)
-- Data.Nat.DivMod._.n′
d_n'8242'_314 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_n'8242'_314 ~v0 v1 v2 ~v3 = du_n'8242'_314 v1 v2
du_n'8242'_314 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
du_n'8242'_314 v0 v1 v2
  = coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1)
-- Data.Nat.DivMod._.k
d_k_316 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_k_316 v0 ~v1 v2 ~v3 = du_k_316 v0 v2
du_k_316 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
du_k_316 v0 v1 v2
  = coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1)
-- Data.Nat.DivMod._.j
d_j_318 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_j_318 ~v0 v1 v2 ~v3 = du_j_318 v1 v2
du_j_318 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
du_j_318 v0 v1 v2
  = coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1)
-- Data.Nat.DivMod._.lemma
d_lemma_320 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_320 = erased
-- Data.Nat.DivMod.%-remove-+ˡ
d_'37''45'remove'45''43''737'_340 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''45'remove'45''43''737'_340 = erased
-- Data.Nat.DivMod.%-remove-+ʳ
d_'37''45'remove'45''43''691'_360 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'37''45'remove'45''43''691'_360 = erased
-- Data.Nat.DivMod./-congˡ
d_'47''45'cong'737'_372 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''45'cong'737'_372 = erased
-- Data.Nat.DivMod./-congʳ
d_'47''45'cong'691'_378 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''45'cong'691'_378 = erased
-- Data.Nat.DivMod.0/n≡0
d_0'47'n'8801'0_384 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'47'n'8801'0_384 = erased
-- Data.Nat.DivMod.n/1≡n
d_n'47'1'8801'n_388 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'47'1'8801'n_388 = erased
-- Data.Nat.DivMod.n/n≡1
d_n'47'n'8801'1_396 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'47'n'8801'1_396 = erased
-- Data.Nat.DivMod.m*n/n≡m
d_m'42'n'47'n'8801'm_406 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'47'n'8801'm_406 = erased
-- Data.Nat.DivMod.m/n*n≡m
d_m'47'n'42'n'8801'm_418 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'47'n'42'n'8801'm_418 = erased
-- Data.Nat.DivMod.m*[n/m]≡n
d_m'42''91'n'47'm'93''8801'n_428 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42''91'n'47'm'93''8801'n_428 = erased
-- Data.Nat.DivMod.m/n*n≤m
d_m'47'n'42'n'8804'm_440 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'47'n'42'n'8804'm_440 v0 v1 ~v2
  = du_m'47'n'42'n'8804'm_440 v0 v1
du_m'47'n'42'n'8804'm_440 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'47'n'42'n'8804'm_440 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
         (\ v2 v3 v4 ->
            coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v4))
      (mulInt
         (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
         (coe v1))
      v0
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
            (\ v2 v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v5
                 v6))
         (mulInt
            (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
            (coe v1))
         (addInt
            (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1))
            (coe
               mulInt
               (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
               (coe v1)))
         v0
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
            (\ v2 v3 v4 v5 v6 -> v6)
            (addInt
               (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1))
               (coe
                  mulInt
                  (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
                  (coe v1)))
            (addInt
               (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1))
               (coe
                  mulInt
                  (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
                  (coe v1)))
            v0
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
               (\ v2 v3 v4 v5 v6 -> v6)
               (addInt
                  (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1))
                  (coe
                     mulInt
                     (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
                     (coe v1)))
               v0 v0
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                  (coe v0))
               erased)
            erased)
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               mulInt
               (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
               (coe v1))))
-- Data.Nat.DivMod.m/n≤m
d_m'47'n'8804'm_452 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'47'n'8804'm_452 v0 v1 ~v2 = du_m'47'n'8804'm_452 v0 v1
du_m'47'n'8804'm_452 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'47'n'8804'm_452 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'42''45'cancel'691''45''8804'_4184
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
-- Data.Nat.DivMod.m/n<m
d_m'47'n'60'm_466 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'47'n'60'm_466 v0 v1 ~v2 ~v3 ~v4 = du_m'47'n'60'm_466 v0 v1
du_m'47'n'60'm_466 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'47'n'60'm_466 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'42''45'cancel'691''45''60'_4338
      (coe v1)
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe v0)
-- Data.Nat.DivMod./-mono-≤
d_'47''45'mono'45''8804'_478 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''45'mono'45''8804'_478 v0 v1 v2 v3 ~v4 ~v5 v6 v7
  = du_'47''45'mono'45''8804'_478 v0 v1 v2 v3 v6 v7
du_'47''45'mono'45''8804'_478 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''45'mono'45''8804'_478 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
        -> let v9 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v10 = subInt (coe v1) (coe (1 :: Integer)) in
              coe
                (coe
                   MAlonzo.Code.Data.Nat.DivMod.Core.d_div'8341''45'mono'45''8804'_886
                   (coe (0 :: Integer)) (coe (0 :: Integer)) (coe v2) (coe v3)
                   (coe v9) (coe v10) (coe v4) (coe v8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.DivMod./-monoˡ-≤
d_'47''45'mono'737''45''8804'_488 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''45'mono'737''45''8804'_488 v0 v1 v2 ~v3 v4
  = du_'47''45'mono'737''45''8804'_488 v0 v1 v2 v4
du_'47''45'mono'737''45''8804'_488 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''45'mono'737''45''8804'_488 v0 v1 v2 v3
  = coe
      du_'47''45'mono'45''8804'_478 (coe v2) (coe v2) (coe v0) (coe v1)
      (coe v3)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v2))
-- Data.Nat.DivMod./-monoʳ-≤
d_'47''45'mono'691''45''8804'_504 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'47''45'mono'691''45''8804'_504 v0 v1 v2 ~v3 ~v4 v5
  = du_'47''45'mono'691''45''8804'_504 v0 v1 v2 v5
du_'47''45'mono'691''45''8804'_504 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'47''45'mono'691''45''8804'_504 v0 v1 v2 v3
  = coe
      du_'47''45'mono'45''8804'_478 (coe v1) (coe v2) (coe v0) (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900 (coe v0))
      (coe v3)
-- Data.Nat.DivMod./-cancelʳ-≡
d_'47''45'cancel'691''45''8801'_518 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''45'cancel'691''45''8801'_518 = erased
-- Data.Nat.DivMod.m<n⇒m/n≡0
d_m'60'n'8658'm'47'n'8801'0_540 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'60'n'8658'm'47'n'8801'0_540 = erased
-- Data.Nat.DivMod.m≥n⇒m/n>0
d_m'8805'n'8658'm'47'n'62'0_554 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8805'n'8658'm'47'n'62'0_554 v0 v1 ~v2 v3
  = du_m'8805'n'8658'm'47'n'62'0_554 v0 v1 v3
du_m'8805'n'8658'm'47'n'62'0_554 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8805'n'8658'm'47'n'62'0_554 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
         (\ v3 v4 v5 ->
            coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v5))
      (1 :: Integer)
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
         (\ v3 v4 v5 v6 v7 -> v7) (1 :: Integer)
         (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v0))
         (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
               (\ v3 v4 v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v6
                    v7))
            (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v0))
            (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
            (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
               (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1)))
            (coe
               du_'47''45'mono'691''45''8804'_504 (coe v0) (coe v0) (coe v1)
               (coe v2)))
         erased)
-- Data.Nat.DivMod.m/n≡0⇒m<n
d_m'47'n'8801'0'8658'm'60'n_568 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'47'n'8801'0'8658'm'60'n_568 v0 v1 ~v2 ~v3
  = du_m'47'n'8801'0'8658'm'60'n_568 v0 v1
du_m'47'n'8801'0'8658'm'60'n_568 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'47'n'8801'0'8658'm'60'n_568 v0 v1
  = let v2 = subInt (coe v1) (coe (1 :: Integer)) in
    coe
      (let v3
             = coe
                 MAlonzo.Code.Data.Sum.Base.du_swap_78
                 (let v3
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            (\ v3 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                 (coe v1))
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                               (coe ltInt (coe v2) (coe v0))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                  (coe ltInt (coe v2) (coe v0)))) in
                  coe
                    (case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then case coe v5 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                                       -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v6)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8816''8658''62'_3032
                                           (coe v1) (coe v0)))
                       _ -> MAlonzo.RTE.mazUnreachableError)) in
       coe
         (case coe v3 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v4
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
              -> coe
                   MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                   erased
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Nat.DivMod.m/n≢0⇒n≤m
d_m'47'n'8802'0'8658'n'8804'm_608 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'47'n'8802'0'8658'n'8804'm_608 v0 v1 ~v2 ~v3
  = du_m'47'n'8802'0'8658'n'8804'm_608 v0 v1
du_m'47'n'8802'0'8658'n'8804'm_608 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'47'n'8802'0'8658'n'8804'm_608 v0 v1
  = let v2 = subInt (coe v1) (coe (1 :: Integer)) in
    coe
      (let v3
             = coe
                 MAlonzo.Code.Data.Sum.Base.du_swap_78
                 (let v3
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            (\ v3 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                 (coe v1))
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                               (coe ltInt (coe v2) (coe v0))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                  (coe ltInt (coe v2) (coe v0)))) in
                  coe
                    (case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then case coe v5 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                                       -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v6)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8816''8658''62'_3032
                                           (coe v1) (coe v0)))
                       _ -> MAlonzo.RTE.mazUnreachableError)) in
       coe
         (case coe v3 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
              -> coe
                   MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                   erased
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4 -> coe v4
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Nat.DivMod.+-distrib-/
d_'43''45'distrib'45''47'_644 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'45''47'_644 = erased
-- Data.Nat.DivMod.+-distrib-/-∣ˡ
d_'43''45'distrib'45''47''45''8739''737'_662 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'45''47''45''8739''737'_662 = erased
-- Data.Nat.DivMod.+-distrib-/-∣ʳ
d_'43''45'distrib'45''47''45''8739''691'_682 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'45''47''45''8739''691'_682 = erased
-- Data.Nat.DivMod.m/n≡1+[m∸n]/n
d_m'47'n'8801'1'43''91'm'8760'n'93''47'n_700 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'47'n'8801'1'43''91'm'8760'n'93''47'n_700 = erased
-- Data.Nat.DivMod.[m∸n]/n≡m/n∸1
d_'91'm'8760'n'93''47'n'8801'm'47'n'8760'1_718 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'8760'n'93''47'n'8801'm'47'n'8760'1_718 = erased
-- Data.Nat.DivMod.m∣n⇒o%n%m≡o%m
d_m'8739'n'8658'o'37'n'37'm'8801'o'37'm_750 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8739'n'8658'o'37'n'37'm'8801'o'37'm_750 = erased
-- Data.Nat.DivMod._.pm
d_pm_764 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_pm_764 v0 ~v1 ~v2 v3 ~v4 = du_pm_764 v0 v3
du_pm_764 :: Integer -> Integer -> Integer
du_pm_764 v0 v1 = coe mulInt (coe v1) (coe v0)
-- Data.Nat.DivMod._.lem
d_lem_766 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lem_766 v0 v1 ~v2 v3 ~v4 = du_lem_766 v0 v1 v3
du_lem_766 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lem_766 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
         (\ v3 v4 v5 ->
            coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v5))
      (mulInt
         (coe
            mulInt
            (coe
               MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
               (coe du_pm_764 (coe v0) (coe v2)))
            (coe v2))
         (coe v0))
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
         (\ v3 v4 v5 v6 v7 -> v7)
         (mulInt
            (coe
               mulInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
                  (coe du_pm_764 (coe v0) (coe v2)))
               (coe v2))
            (coe v0))
         (mulInt
            (coe
               MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
               (coe du_pm_764 (coe v0) (coe v2)))
            (coe du_pm_764 (coe v0) (coe v2)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
               (\ v3 v4 v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v6
                    v7))
            (mulInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
                  (coe du_pm_764 (coe v0) (coe v2)))
               (coe du_pm_764 (coe v0) (coe v2)))
            v1 v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
               (coe v1))
            (coe
               du_m'47'n'42'n'8804'm_440 (coe v1)
               (coe du_pm_764 (coe v0) (coe v2))))
         erased)
-- Data.Nat.DivMod.m*n/m*o≡n/o
d_m'42'n'47'm'42'o'8801'n'47'o_780 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'47'm'42'o'8801'n'47'o_780 = erased
-- Data.Nat.DivMod._.helper
d_helper_796 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_796 = erased
-- Data.Nat.DivMod._._.n∸o<n
d_n'8760'o'60'n_828 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8760'o'60'n_828 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_n'8760'o'60'n_828 v0 v1 v2
du_n'8760'o'60'n_828 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8760'o'60'n_828 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8760''45'mono'691''45''60'_5276
      (coe v1) (coe v0) (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_n'8802'0'8658'n'62'0_3232
         (coe v0))
      (coe v2)
-- Data.Nat.DivMod.m*n/o*n≡m/o
d_m'42'n'47'o'42'n'8801'm'47'o_842 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'47'o'42'n'8801'm'47'o_842 = erased
-- Data.Nat.DivMod.m<n*o⇒m/o<n
d_m'60'n'42'o'8658'm'47'o'60'n_866 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'42'o'8658'm'47'o'60'n_866 v0 v1 v2 ~v3 ~v4
  = du_m'60'n'42'o'8658'm'47'o'60'n_866 v0 v1 v2
du_m'60'n'42'o'8658'm'47'o'60'n_866 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'42'o'8658'm'47'o'60'n_866 v0 v1 v2
  = case coe v1 of
      1 -> let v3 = mulInt (coe (1 :: Integer)) (coe v2) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v3))
                (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                   (\ v4 v5 v6 v7 v8 -> v8)
                   (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v3))
                   (0 :: Integer) (1 :: Integer)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                         (\ v4 v5 v6 v7 v8 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 v5 v7 v8)
                         (coe
                            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                         (\ v4 v5 v6 v7 v8 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134 v7
                              v8))
                      (0 :: Integer) (1 :: Integer) (1 :: Integer)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                         (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                   erased))
      _ -> coe
             MAlonzo.Code.Data.Nat.Properties.d_pred'45'cancel'45''60'_5828
             (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v2)) v1
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                (coe
                   MAlonzo.Code.Data.Nat.Base.d_pred_196
                   (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v2)))
                (coe subInt (coe v1) (coe (1 :: Integer)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                   (\ v3 v4 v5 v6 v7 -> v7)
                   (MAlonzo.Code.Data.Nat.Base.d_pred_196
                      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v2)))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.du__'47'__318
                      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v2) (coe v2))
                   (subInt (coe v1) (coe (1 :: Integer)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                         (\ v3 v4 v5 v6 v7 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 v4 v6 v7)
                         (coe
                            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                         (\ v3 v4 v5 v6 v7 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134 v6
                              v7))
                      (coe
                         MAlonzo.Code.Data.Nat.Base.du__'47'__318
                         (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v2) (coe v2))
                      (subInt (coe v1) (coe (1 :: Integer)))
                      (subInt (coe v1) (coe (1 :: Integer)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                         (coe subInt (coe v1) (coe (1 :: Integer))))
                      (coe
                         du_m'60'n'42'o'8658'm'47'o'60'n_866
                         (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v2)
                         (coe subInt (coe v1) (coe (1 :: Integer))) (coe v2)))
                   erased))
-- Data.Nat.DivMod.[m∸n*o]/o≡m/o∸n
d_'91'm'8760'n'42'o'93''47'o'8801'm'47'o'8760'n_900 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'8760'n'42'o'93''47'o'8801'm'47'o'8760'n_900 = erased
-- Data.Nat.DivMod.m/n/o≡m/[n*o]
d_m'47'n'47'o'8801'm'47''91'n'42'o'93'_926 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'47'n'47'o'8801'm'47''91'n'42'o'93'_926 = erased
-- Data.Nat.DivMod._.n*o
d_n'42'o_938 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_n'42'o_938 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_n'42'o_938 v1 v2
du_n'42'o_938 :: Integer -> Integer -> Integer
du_n'42'o_938 v0 v1 = coe mulInt (coe v0) (coe v1)
-- Data.Nat.DivMod._.o*n
d_o'42'n_940 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_o'42'n_940 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_o'42'n_940 v1 v2
du_o'42'n_940 :: Integer -> Integer -> Integer
du_o'42'n_940 v0 v1 = coe mulInt (coe v1) (coe v0)
-- Data.Nat.DivMod._.lem₁
d_lem'8321'_942 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_lem'8321'_942 v0 v1 v2 ~v3 ~v4 ~v5 = du_lem'8321'_942 v0 v1 v2
du_lem'8321'_942 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_lem'8321'_942 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
      (mulInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0)
            (coe du_n'42'o_938 (coe v1) (coe v2)))
         (coe v2))
-- Data.Nat.DivMod._.lem₂
d_lem'8322'_946 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'8322'_946 = erased
-- Data.Nat.DivMod._.lem₃
d_lem'8323'_950 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lem'8323'_950 v0 v1 v2 ~v3 ~v4 ~v5 = du_lem'8323'_950 v0 v1 v2
du_lem'8323'_950 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lem'8323'_950 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0)
         (coe du_n'42'o_938 (coe v1) (coe v2)))
      (coe du_o'42'n_940 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
            (\ v3 v4 v5 v6 v7 ->
               coe
                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 v4 v6 v7)
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
            (\ v3 v4 v5 v6 v7 ->
               coe
                 MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134 v6
                 v7))
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0)
            (coe du_n'42'o_938 (coe v1) (coe v2)))
         (coe du_n'42'o_938 (coe v1) (coe v2))
         (coe du_o'42'n_940 (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
            (\ v3 v4 v5 v6 v7 -> v7) (coe du_n'42'o_938 (coe v1) (coe v2))
            (coe du_o'42'n_940 (coe v1) (coe v2))
            (coe du_o'42'n_940 (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
               (coe du_o'42'n_940 (coe v1) (coe v2)))
            erased)
         (coe
            du_m'37'n'60'n_166 (coe v0) (coe du_n'42'o_938 (coe v1) (coe v2))))
-- Data.Nat.DivMod.*-/-assoc
d_'42''45''47''45'assoc_966 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45''47''45'assoc_966 = erased
-- Data.Nat.DivMod./-*-interchange
d_'47''45''42''45'interchange_988 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''45''42''45'interchange_988 = erased
-- Data.Nat.DivMod.m*n/m!≡n/[m∸1]!
d_m'42'n'47'm'33''8801'n'47''91'm'8760'1'93''33'_1012 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'47'm'33''8801'n'47''91'm'8760'1'93''33'_1012 = erased
-- Data.Nat.DivMod.m%[n*o]/o≡m/o%n
d_m'37''91'n'42'o'93''47'o'8801'm'47'o'37'n_1040 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'37''91'n'42'o'93''47'o'8801'm'47'o'37'n_1040 = erased
-- Data.Nat.DivMod.m%n*o≡m*o%[n*o]
d_m'37'n'42'o'8801'm'42'o'37''91'n'42'o'93'_1070 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'37'n'42'o'8801'm'42'o'37''91'n'42'o'93'_1070 = erased
-- Data.Nat.DivMod.[m*n+o]%[p*n]≡[m*n]%[p*n]+o
d_'91'm'42'n'43'o'93''37''91'p'42'n'93''8801''91'm'42'n'93''37''91'p'42'n'93''43'o_1094 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'42'n'43'o'93''37''91'p'42'n'93''8801''91'm'42'n'93''37''91'p'42'n'93''43'o_1094
  = erased
-- Data.Nat.DivMod._.mn
d_mn_1112 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_mn_1112 v0 v1 ~v2 ~v3 ~v4 ~v5 = du_mn_1112 v0 v1
du_mn_1112 :: Integer -> Integer -> Integer
du_mn_1112 v0 v1 = coe mulInt (coe v0) (coe v1)
-- Data.Nat.DivMod._.pn
d_pn_1114 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> Integer
d_pn_1114 ~v0 v1 ~v2 v3 ~v4 ~v5 = du_pn_1114 v1 v3
du_pn_1114 :: Integer -> Integer -> Integer
du_pn_1114 v0 v1
  = coe mulInt (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v0)
-- Data.Nat.DivMod._.lem₁
d_lem'8321'_1116 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lem'8321'_1116 v0 v1 ~v2 v3 ~v4 ~v5 = du_lem'8321'_1116 v0 v1 v3
du_lem'8321'_1116 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lem'8321'_1116 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
         (\ v3 v4 v5 ->
            coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v5))
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'37'__330
         (coe du_mn_1112 (coe v0) (coe v1))
         (coe du_pn_1114 (coe v1) (coe v2)))
      (mulInt (coe v2) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
         (\ v3 v4 v5 v6 v7 -> v7)
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'37'__330
            (coe du_mn_1112 (coe v0) (coe v1))
            (coe du_pn_1114 (coe v1) (coe v2)))
         (mulInt
            (coe
               MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0)
               (coe addInt (coe (1 :: Integer)) (coe v2)))
            (coe v1))
         (mulInt (coe v2) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
               (\ v3 v4 v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v6
                    v7))
            (mulInt
               (coe
                  MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0)
                  (coe addInt (coe (1 :: Integer)) (coe v2)))
               (coe v1))
            (mulInt (coe v2) (coe v1)) (mulInt (coe v2) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
               (coe mulInt (coe v2) (coe v1)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'737''45''8804'_4222
               v1 (remInt (coe v0) (coe addInt (coe (1 :: Integer)) (coe v2))) v2
               (coe
                  MAlonzo.Code.Data.Nat.Properties.du_m'60'1'43'n'8658'm'8804'n_3264
                  (coe
                     du_m'37'n'60'n_166 (coe v0)
                     (coe addInt (coe (1 :: Integer)) (coe v2))))))
         erased)
-- Data.Nat.DivMod._.lem₂
d_lem'8322'_1118 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lem'8322'_1118 v0 v1 v2 v3 ~v4 v5
  = du_lem'8322'_1118 v0 v1 v2 v3 v5
du_lem'8322'_1118 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lem'8322'_1118 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
      (coe
         addInt
         (coe
            MAlonzo.Code.Data.Nat.Base.du__'37'__330
            (coe du_mn_1112 (coe v0) (coe v1))
            (coe du_pn_1114 (coe v1) (coe v3)))
         (coe v2))
      (coe du_pn_1114 (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
            (\ v5 v6 v7 v8 v9 ->
               coe
                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 v6 v8 v9)
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
            (\ v5 v6 v7 v8 v9 ->
               coe
                 MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134 v8
                 v9))
         (addInt
            (coe
               MAlonzo.Code.Data.Nat.Base.du__'37'__330
               (coe du_mn_1112 (coe v0) (coe v1))
               (coe du_pn_1114 (coe v1) (coe v3)))
            (coe v2))
         (addInt (coe mulInt (coe v3) (coe v1)) (coe v1))
         (coe du_pn_1114 (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
            (\ v5 v6 v7 v8 v9 -> v9)
            (addInt (coe mulInt (coe v3) (coe v1)) (coe v1))
            (coe du_pn_1114 (coe v1) (coe v3))
            (coe du_pn_1114 (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
               (coe du_pn_1114 (coe v1) (coe v3)))
            erased)
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'45''8804''45''60'_3696
            (coe v1) (coe du_lem'8321'_1116 (coe v0) (coe v1) (coe v3))
            (coe v4)))
-- Data.Nat.DivMod.DivMod
d_DivMod_1126 a0 a1 = ()
data T_DivMod_1126
  = C_result_1146 Integer MAlonzo.Code.Data.Fin.Base.T_Fin_10
-- Data.Nat.DivMod.DivMod.quotient
d_quotient_1138 :: T_DivMod_1126 -> Integer
d_quotient_1138 v0
  = case coe v0 of
      C_result_1146 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.DivMod.DivMod.remainder
d_remainder_1140 ::
  T_DivMod_1126 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_remainder_1140 v0
  = case coe v0 of
      C_result_1146 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.DivMod.DivMod.property
d_property_1142 ::
  T_DivMod_1126 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_property_1142 = erased
-- Data.Nat.DivMod.DivMod.nonZeroDivisor
d_nonZeroDivisor_1144 ::
  Integer ->
  Integer ->
  T_DivMod_1126 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_nonZeroDivisor_1144 ~v0 ~v1 ~v2 = du_nonZeroDivisor_1144
du_nonZeroDivisor_1144 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_nonZeroDivisor_1144
  = coe MAlonzo.Code.Data.Fin.Properties.du_nonZeroIndex_22
-- Data.Nat.DivMod._div_
d__div__1154 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__div__1154 v0 v1 v2
  = coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 v0 v1
-- Data.Nat.DivMod._mod_
d__mod__1162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d__mod__1162 v0 v1 ~v2 = du__mod__1162 v0 v1
du__mod__1162 ::
  Integer -> Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
du__mod__1162 v0 v1
  = coe
      MAlonzo.Code.Data.Fin.Base.du_fromℕ'60'_52
      (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1))
-- Data.Nat.DivMod._divMod_
d__divMod__1174 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_DivMod_1126
d__divMod__1174 v0 v1 ~v2 = du__divMod__1174 v0 v1
du__divMod__1174 :: Integer -> Integer -> T_DivMod_1126
du__divMod__1174 v0 v1
  = coe
      C_result_1146
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe du__mod__1162 (coe v0) (coe v1))
-- Data.Nat.DivMod._.[m/n]*n
d_'91'm'47'n'93''42'n_1184 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d_'91'm'47'n'93''42'n_1184 v0 v1 ~v2
  = du_'91'm'47'n'93''42'n_1184 v0 v1
du_'91'm'47'n'93''42'n_1184 :: Integer -> Integer -> Integer
du_'91'm'47'n'93''42'n_1184 v0 v1
  = coe
      mulInt
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe v1)
-- Data.Nat.DivMod._.[m%n]<n
d_'91'm'37'n'93''60'n_1186 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'91'm'37'n'93''60'n_1186 v0 v1 ~v2
  = du_'91'm'37'n'93''60'n_1186 v0 v1
du_'91'm'37'n'93''60'n_1186 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'91'm'37'n'93''60'n_1186 v0 v1 v2
  = coe du_m'37'n'60'n_166 (coe v0) (coe v1)
