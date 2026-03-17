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

module MAlonzo.Code.Data.Rational.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.GCD
import qualified MAlonzo.Code.Data.Rational.Unnormalised.Base
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core

-- Data.Rational.Base.ℚ
d_ℚ_6 = ()
data T_ℚ_6 = C_mkℚ_24 Integer Integer
-- Data.Rational.Base.ℚ.numerator
d_numerator_14 :: T_ℚ_6 -> Integer
d_numerator_14 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.ℚ.denominator-1
d_denominator'45'1_16 :: T_ℚ_6 -> Integer
d_denominator'45'1_16 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.ℚ.denominatorℕ
d_denominatorℕ_20 :: T_ℚ_6 -> Integer
d_denominatorℕ_20 v0
  = coe
      addInt (coe (1 :: Integer)) (coe d_denominator'45'1_16 (coe v0))
-- Data.Rational.Base.ℚ.denominator
d_denominator_22 :: T_ℚ_6 -> Integer
d_denominator_22 v0 = coe d_denominatorℕ_20 (coe v0)
-- Data.Rational.Base.mkℚ+
d_mkℚ'43'_32 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_ℚ_6
d_mkℚ'43'_32 v0 v1 ~v2 ~v3 = du_mkℚ'43'_32 v0 v1
du_mkℚ'43'_32 :: Integer -> Integer -> T_ℚ_6
du_mkℚ'43'_32 v0 v1
  = let v2 = subInt (coe v1) (coe (1 :: Integer)) in
    coe (coe C_mkℚ_24 v0 v2)
-- Data.Rational.Base._≃_
d__'8771'__40 a0 a1 = ()
data T__'8771'__40 = C_'42''8801''42'_46
-- Data.Rational.Base._≄_
d__'8772'__48 :: T_ℚ_6 -> T_ℚ_6 -> ()
d__'8772'__48 = erased
-- Data.Rational.Base._≤_
d__'8804'__54 a0 a1 = ()
newtype T__'8804'__54
  = C_'42''8804''42'_60 MAlonzo.Code.Data.Integer.Base.T__'8804'__26
-- Data.Rational.Base._<_
d__'60'__62 a0 a1 = ()
newtype T__'60'__62
  = C_'42''60''42'_68 MAlonzo.Code.Data.Integer.Base.T__'60'__50
-- Data.Rational.Base._≥_
d__'8805'__70 :: T_ℚ_6 -> T_ℚ_6 -> ()
d__'8805'__70 = erased
-- Data.Rational.Base._>_
d__'62'__76 :: T_ℚ_6 -> T_ℚ_6 -> ()
d__'62'__76 = erased
-- Data.Rational.Base._≰_
d__'8816'__82 :: T_ℚ_6 -> T_ℚ_6 -> ()
d__'8816'__82 = erased
-- Data.Rational.Base._≱_
d__'8817'__88 :: T_ℚ_6 -> T_ℚ_6 -> ()
d__'8817'__88 = erased
-- Data.Rational.Base._≮_
d__'8814'__94 :: T_ℚ_6 -> T_ℚ_6 -> ()
d__'8814'__94 = erased
-- Data.Rational.Base._≯_
d__'8815'__100 :: T_ℚ_6 -> T_ℚ_6 -> ()
d__'8815'__100 = erased
-- Data.Rational.Base._≤ᵇ_
d__'8804''7495'__106 :: T_ℚ_6 -> T_ℚ_6 -> Bool
d__'8804''7495'__106 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe d_numerator_14 (coe v0)) (coe d_denominator_22 (coe v1)))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe d_numerator_14 (coe v1)) (coe d_denominator_22 (coe v0)))
-- Data.Rational.Base.-_
d_'45'__112 :: T_ℚ_6 -> T_ℚ_6
d_'45'__112 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2
        -> coe
             seq (coe v1)
             (coe C_mkℚ_24 (subInt (coe (0 :: Integer)) (coe v1)) v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.normalize
d_normalize_136 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_ℚ_6
d_normalize_136 v0 v1 ~v2 = du_normalize_136 v0 v1
du_normalize_136 :: Integer -> Integer -> T_ℚ_6
du_normalize_136 v0 v1
  = coe
      du_mkℚ'43'_32
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__314 (coe v0)
         (coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.Nat.Base.du__'47'__314 (coe v1)
         (coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1)))
-- Data.Rational.Base._.g≢0
d_g'8802'0_146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_g'8802'0_146 v0 v1 ~v2 = du_g'8802'0_146 v0 v1
du_g'8802'0_146 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_g'8802'0_146 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'8802''45'nonZero_126
      (coe MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe v0) (coe v1))
-- Data.Rational.Base._/_
d__'47'__156 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_ℚ_6
d__'47'__156 v0 v1 ~v2 = du__'47'__156 v0 v1
du__'47'__156 :: Integer -> Integer -> T_ℚ_6
du__'47'__156 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_normalize_136 (coe v0) (coe v1)
      _ -> coe
             d_'45'__112
             (coe
                du_normalize_136 (coe subInt (coe (0 :: Integer)) (coe v0))
                (coe v1))
-- Data.Rational.Base.toℚᵘ
d_toℚ'7512'_166 ::
  T_ℚ_6 -> MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8
d_toℚ'7512'_166 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2
        -> coe
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.fromℚᵘ
d_fromℚ'7512'_172 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> T_ℚ_6
d_fromℚ'7512'_172 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> coe
             du__'47'__156 (coe v1) (coe addInt (coe (1 :: Integer)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.0ℚ
d_0ℚ_178 :: T_ℚ_6
d_0ℚ_178
  = coe du__'47'__156 (coe (0 :: Integer)) (coe (1 :: Integer))
-- Data.Rational.Base.1ℚ
d_1ℚ_180 :: T_ℚ_6
d_1ℚ_180
  = coe du__'47'__156 (coe (1 :: Integer)) (coe (1 :: Integer))
-- Data.Rational.Base.½
d_'189'_182 :: T_ℚ_6
d_'189'_182
  = coe du__'47'__156 (coe (1 :: Integer)) (coe (2 :: Integer))
-- Data.Rational.Base.-½
d_'45''189'_184 :: T_ℚ_6
d_'45''189'_184 = coe d_'45'__112 (coe d_'189'_182)
-- Data.Rational.Base.NonZero
d_NonZero_186 :: T_ℚ_6 -> ()
d_NonZero_186 = erased
-- Data.Rational.Base.Positive
d_Positive_190 :: T_ℚ_6 -> ()
d_Positive_190 = erased
-- Data.Rational.Base.Negative
d_Negative_194 :: T_ℚ_6 -> ()
d_Negative_194 = erased
-- Data.Rational.Base.NonPositive
d_NonPositive_198 :: T_ℚ_6 -> ()
d_NonPositive_198 = erased
-- Data.Rational.Base.NonNegative
d_NonNegative_202 :: T_ℚ_6 -> ()
d_NonNegative_202 = erased
-- Data.Rational.Base.≢-nonZero
d_'8802''45'nonZero_208 ::
  T_ℚ_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'8802''45'nonZero_208 v0 ~v1 = du_'8802''45'nonZero_208 v0
du_'8802''45'nonZero_208 ::
  T_ℚ_6 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_'8802''45'nonZero_208 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2
        -> case coe v1 of
             0 -> coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased)
             _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                 coe
                   MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> coe
                    MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.>-nonZero
d_'62''45'nonZero_224 ::
  T_ℚ_6 -> T__'60'__62 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'62''45'nonZero_224 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_'42''60''42'_68 v7
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'62''45'nonZero_148
                    (coe d_toℚ'7512'_166 (coe C_mkℚ_24 v2 v3))
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.<-nonZero
d_'60''45'nonZero_232 ::
  T_ℚ_6 -> T__'60'__62 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'60''45'nonZero_232 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_'42''60''42'_68 v7
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'60''45'nonZero_154
                    (coe d_toℚ'7512'_166 (coe C_mkℚ_24 v2 v3))
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.positive
d_positive_240 ::
  T_ℚ_6 ->
  T__'60'__62 -> MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_positive_240 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_'42''60''42'_68 v7
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_positive_162
                    (coe d_toℚ'7512'_166 (coe C_mkℚ_24 v2 v3))
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.negative
d_negative_248 ::
  T_ℚ_6 ->
  T__'60'__62 -> MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_negative_248 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_'42''60''42'_68 v7
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_negative_170
                    (coe d_toℚ'7512'_166 (coe C_mkℚ_24 v2 v3))
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.nonPositive
d_nonPositive_256 ::
  T_ℚ_6 ->
  T__'8804'__54 -> MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
d_nonPositive_256 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_'42''8804''42'_60 v7
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_nonPositive_178
                    (coe d_toℚ'7512'_166 (coe C_mkℚ_24 v2 v3))
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                       v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.nonNegative
d_nonNegative_264 ::
  T_ℚ_6 ->
  T__'8804'__54 -> MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_nonNegative_264 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_'42''8804''42'_60 v7
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_nonNegative_186
                    (coe d_toℚ'7512'_166 (coe C_mkℚ_24 v2 v3))
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                       v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base._+_
d__'43'__270 :: T_ℚ_6 -> T_ℚ_6 -> T_ℚ_6
d__'43'__270 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_mkℚ_24 v5 v6
               -> coe
                    du__'47'__156
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'43'__276
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2)
                          (coe d_denominator_22 (coe C_mkℚ_24 v5 v6)))
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                          (coe d_denominator_22 (coe C_mkℚ_24 v2 v3))))
                    (coe
                       mulInt (coe d_denominatorℕ_20 (coe C_mkℚ_24 v2 v3))
                       (coe d_denominatorℕ_20 (coe C_mkℚ_24 v5 v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base._*_
d__'42'__276 :: T_ℚ_6 -> T_ℚ_6 -> T_ℚ_6
d__'42'__276 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_mkℚ_24 v5 v6
               -> coe
                    du__'47'__156
                    (coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2) (coe v5))
                    (coe
                       mulInt (coe d_denominatorℕ_20 (coe C_mkℚ_24 v2 v3))
                       (coe d_denominatorℕ_20 (coe C_mkℚ_24 v5 v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base._-_
d__'45'__282 :: T_ℚ_6 -> T_ℚ_6 -> T_ℚ_6
d__'45'__282 v0 v1
  = coe d__'43'__270 (coe v0) (coe d_'45'__112 (coe v1))
-- Data.Rational.Base.1/_
d_1'47'__292 ::
  T_ℚ_6 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_ℚ_6
d_1'47'__292 v0 ~v1 = du_1'47'__292 v0
du_1'47'__292 :: T_ℚ_6 -> T_ℚ_6
du_1'47'__292 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2
        -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                 let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                 coe (coe C_mkℚ_24 (addInt (coe (1 :: Integer)) (coe v2)) v4)
             _ -> let v4 = subInt (coe (-1 :: Integer)) (coe v1) in
                  coe (coe C_mkℚ_24 (subInt (coe (-1 :: Integer)) (coe v2)) v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base._÷_
d__'247'__312 ::
  T_ℚ_6 -> T_ℚ_6 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_ℚ_6
d__'247'__312 v0 v1 ~v2 = du__'247'__312 v0 v1
du__'247'__312 :: T_ℚ_6 -> T_ℚ_6 -> T_ℚ_6
du__'247'__312 v0 v1
  = coe d__'42'__276 (coe v0) (coe du_1'47'__292 (coe v1))
-- Data.Rational.Base._⊔_
d__'8852'__322 :: T_ℚ_6 -> T_ℚ_6 -> T_ℚ_6
d__'8852'__322 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_mkℚ_24 v5 v6
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       d__'8804''7495'__106 (coe C_mkℚ_24 v2 v3) (coe C_mkℚ_24 v5 v6))
                    (coe C_mkℚ_24 v5 v6) (coe C_mkℚ_24 v2 v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base._⊓_
d__'8851'__332 :: T_ℚ_6 -> T_ℚ_6 -> T_ℚ_6
d__'8851'__332 v0 v1
  = case coe v0 of
      C_mkℚ_24 v2 v3
        -> case coe v1 of
             C_mkℚ_24 v5 v6
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       d__'8804''7495'__106 (coe C_mkℚ_24 v2 v3) (coe C_mkℚ_24 v5 v6))
                    (coe C_mkℚ_24 v2 v3) (coe C_mkℚ_24 v5 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.∣_∣
d_'8739'_'8739'_338 :: T_ℚ_6 -> T_ℚ_6
d_'8739'_'8739'_338 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2
        -> coe
             C_mkℚ_24
             (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)) v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.floor
d_floor_346 :: T_ℚ_6 -> Integer
d_floor_346 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2
        -> coe
             MAlonzo.Code.Data.Integer.Base.du__'47'__394 (coe v1)
             (coe d_denominator_22 (coe C_mkℚ_24 v1 v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.ceiling
d_ceiling_350 :: T_ℚ_6 -> Integer
d_ceiling_350 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2
        -> coe
             MAlonzo.Code.Data.Integer.Base.d_'45'__252
             (coe d_floor_346 (coe d_'45'__112 (coe C_mkℚ_24 v1 v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.truncate
d_truncate_354 :: T_ℚ_6 -> Integer
d_truncate_354 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d__'8804''7495'__106 (coe v0) (coe d_0ℚ_178))
      (coe d_ceiling_350 (coe v0)) (coe d_floor_346 (coe v0))
-- Data.Rational.Base.round
d_round_358 :: T_ℚ_6 -> Integer
d_round_358 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d__'8804''7495'__106 (coe v0) (coe d_0ℚ_178))
      (coe d_ceiling_350 (coe d__'45'__282 (coe v0) (coe d_'189'_182)))
      (coe d_floor_346 (coe d__'43'__270 (coe v0) (coe d_'189'_182)))
-- Data.Rational.Base.fracPart
d_fracPart_362 :: T_ℚ_6 -> T_ℚ_6
d_fracPart_362 v0
  = case coe v0 of
      C_mkℚ_24 v1 v2
        -> coe
             d_'8739'_'8739'_338
             (coe
                d__'45'__282 (coe C_mkℚ_24 v1 v2)
                (coe
                   du__'47'__156 (coe d_truncate_354 (coe C_mkℚ_24 v1 v2))
                   (coe (1 :: Integer))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Base.+-rawMagma
d_'43''45'rawMagma_366 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'43''45'rawMagma_366
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_487
      d__'43'__270
-- Data.Rational.Base.+-0-rawMonoid
d_'43''45'0'45'rawMonoid_368 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'43''45'0'45'rawMonoid_368
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_857
      d__'43'__270 d_0ℚ_178
-- Data.Rational.Base.+-0-rawGroup
d_'43''45'0'45'rawGroup_370 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_102
d_'43''45'0'45'rawGroup_370
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawGroup'46'constructor_1319
      d__'43'__270 d_0ℚ_178 d_'45'__112
-- Data.Rational.Base.+-*-rawNearSemiring
d_'43''45''42''45'rawNearSemiring_372 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_140
d_'43''45''42''45'rawNearSemiring_372
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawNearSemiring'46'constructor_1841
      d__'43'__270 d__'42'__276 d_0ℚ_178
-- Data.Rational.Base.+-*-rawSemiring
d_'43''45''42''45'rawSemiring_374 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_180
d_'43''45''42''45'rawSemiring_374
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawSemiring'46'constructor_2465
      d__'43'__270 d__'42'__276 d_0ℚ_178 d_1ℚ_180
-- Data.Rational.Base.+-*-rawRing
d_'43''45''42''45'rawRing_376 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
d_'43''45''42''45'rawRing_376
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawRing'46'constructor_3989
      d__'43'__270 d__'42'__276 d_'45'__112 d_0ℚ_178 d_1ℚ_180
-- Data.Rational.Base.*-rawMagma
d_'42''45'rawMagma_378 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'42''45'rawMagma_378
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_487
      d__'42'__276
-- Data.Rational.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_380 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'42''45'1'45'rawMonoid_380
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_857
      d__'42'__276 d_1ℚ_180
-- Data.Rational.Base.+-rawMonoid
d_'43''45'rawMonoid_382 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'43''45'rawMonoid_382 = coe d_'43''45'0'45'rawMonoid_368
-- Data.Rational.Base.*-rawMonoid
d_'42''45'rawMonoid_384 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'42''45'rawMonoid_384 = coe d_'42''45'1'45'rawMonoid_380
