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

module MAlonzo.Code.Data.Rational.Unnormalised.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core

-- Data.Rational.Unnormalised.Base.ℚᵘ
d_ℚ'7512'_8 = ()
data T_ℚ'7512'_8 = C_mkℚ'7512'_22 Integer Integer
-- Data.Rational.Unnormalised.Base.ℚᵘ.numerator
d_numerator_14 :: T_ℚ'7512'_8 -> Integer
d_numerator_14 v0
  = case coe v0 of
      C_mkℚ'7512'_22 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base.ℚᵘ.denominator-1
d_denominator'45'1_16 :: T_ℚ'7512'_8 -> Integer
d_denominator'45'1_16 v0
  = case coe v0 of
      C_mkℚ'7512'_22 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base.ℚᵘ.denominatorℕ
d_denominatorℕ_18 :: T_ℚ'7512'_8 -> Integer
d_denominatorℕ_18 v0
  = coe
      addInt (coe (1 :: Integer)) (coe d_denominator'45'1_16 (coe v0))
-- Data.Rational.Unnormalised.Base.ℚᵘ.denominator
d_denominator_20 :: T_ℚ'7512'_8 -> Integer
d_denominator_20 v0 = coe d_denominatorℕ_18 (coe v0)
-- Data.Rational.Unnormalised.Base._≃_
d__'8771'__24 a0 a1 = ()
data T__'8771'__24 = C_'42''8801''42'_30
-- Data.Rational.Unnormalised.Base._≄_
d__'8772'__32 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> ()
d__'8772'__32 = erased
-- Data.Rational.Unnormalised.Base._≤_
d__'8804'__38 a0 a1 = ()
newtype T__'8804'__38
  = C_'42''8804''42'_44 MAlonzo.Code.Data.Integer.Base.T__'8804'__26
-- Data.Rational.Unnormalised.Base._<_
d__'60'__46 a0 a1 = ()
newtype T__'60'__46
  = C_'42''60''42'_52 MAlonzo.Code.Data.Integer.Base.T__'60'__50
-- Data.Rational.Unnormalised.Base._≥_
d__'8805'__54 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> ()
d__'8805'__54 = erased
-- Data.Rational.Unnormalised.Base._>_
d__'62'__60 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> ()
d__'62'__60 = erased
-- Data.Rational.Unnormalised.Base._≰_
d__'8816'__66 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> ()
d__'8816'__66 = erased
-- Data.Rational.Unnormalised.Base._≱_
d__'8817'__72 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> ()
d__'8817'__72 = erased
-- Data.Rational.Unnormalised.Base._≮_
d__'8814'__78 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> ()
d__'8814'__78 = erased
-- Data.Rational.Unnormalised.Base._≯_
d__'8815'__84 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> ()
d__'8815'__84 = erased
-- Data.Rational.Unnormalised.Base._≤ᵇ_
d__'8804''7495'__90 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> Bool
d__'8804''7495'__90 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe d_numerator_14 (coe v0)) (coe d_denominator_20 (coe v1)))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe d_numerator_14 (coe v1)) (coe d_denominator_20 (coe v0)))
-- Data.Rational.Unnormalised.Base._/_
d__'47'__102 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_ℚ'7512'_8
d__'47'__102 v0 v1 ~v2 = du__'47'__102 v0 v1
du__'47'__102 :: Integer -> Integer -> T_ℚ'7512'_8
du__'47'__102 v0 v1
  = let v2 = subInt (coe v1) (coe (1 :: Integer)) in
    coe (coe C_mkℚ'7512'_22 (coe v0) (coe v2))
-- Data.Rational.Unnormalised.Base.0ℚᵘ
d_0ℚ'7512'_108 :: T_ℚ'7512'_8
d_0ℚ'7512'_108
  = coe du__'47'__102 (coe (0 :: Integer)) (coe (1 :: Integer))
-- Data.Rational.Unnormalised.Base.1ℚᵘ
d_1ℚ'7512'_110 :: T_ℚ'7512'_8
d_1ℚ'7512'_110
  = coe du__'47'__102 (coe (1 :: Integer)) (coe (1 :: Integer))
-- Data.Rational.Unnormalised.Base.½
d_'189'_112 :: T_ℚ'7512'_8
d_'189'_112
  = coe du__'47'__102 (coe (1 :: Integer)) (coe (2 :: Integer))
-- Data.Rational.Unnormalised.Base.-½
d_'45''189'_114 :: T_ℚ'7512'_8
d_'45''189'_114
  = coe
      du__'47'__102
      (coe
         MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe (1 :: Integer)))
      (coe (2 :: Integer))
-- Data.Rational.Unnormalised.Base.NonZero
d_NonZero_116 :: T_ℚ'7512'_8 -> ()
d_NonZero_116 = erased
-- Data.Rational.Unnormalised.Base.Positive
d_Positive_120 :: T_ℚ'7512'_8 -> ()
d_Positive_120 = erased
-- Data.Rational.Unnormalised.Base.Negative
d_Negative_124 :: T_ℚ'7512'_8 -> ()
d_Negative_124 = erased
-- Data.Rational.Unnormalised.Base.NonPositive
d_NonPositive_128 :: T_ℚ'7512'_8 -> ()
d_NonPositive_128 = erased
-- Data.Rational.Unnormalised.Base.NonNegative
d_NonNegative_132 :: T_ℚ'7512'_8 -> ()
d_NonNegative_132 = erased
-- Data.Rational.Unnormalised.Base.≢-nonZero
d_'8802''45'nonZero_138 ::
  T_ℚ'7512'_8 ->
  (T__'8771'__24 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'8802''45'nonZero_138 v0 ~v1 = du_'8802''45'nonZero_138 v0
du_'8802''45'nonZero_138 ::
  T_ℚ'7512'_8 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_'8802''45'nonZero_138 v0
  = case coe v0 of
      C_mkℚ'7512'_22 v1 v2
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
-- Data.Rational.Unnormalised.Base.>-nonZero
d_'62''45'nonZero_148 ::
  T_ℚ'7512'_8 ->
  T__'60'__46 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'62''45'nonZero_148 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.Rational.Unnormalised.Base.<-nonZero
d_'60''45'nonZero_154 ::
  T_ℚ'7512'_8 ->
  T__'60'__46 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'60''45'nonZero_154 v0 v1
  = case coe v0 of
      C_mkℚ'7512'_22 v2 v3
        -> coe
             seq (coe v2)
             (coe
                seq (coe v1)
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base.positive
d_positive_162 ::
  T_ℚ'7512'_8 ->
  T__'60'__46 -> MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_positive_162 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Integer.Base.C_Positive'46'constructor_1399
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.Rational.Unnormalised.Base.negative
d_negative_170 ::
  T_ℚ'7512'_8 ->
  T__'60'__46 -> MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_negative_170 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Integer.Base.C_Negative'46'constructor_1573
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.Rational.Unnormalised.Base.nonPositive
d_nonPositive_178 ::
  T_ℚ'7512'_8 ->
  T__'8804'__38 -> MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
d_nonPositive_178 v0 v1
  = case coe v0 of
      C_mkℚ'7512'_22 v2 v3
        -> coe
             seq (coe v2)
             (coe
                seq (coe v1)
                (coe
                   MAlonzo.Code.Data.Integer.Base.C_NonPositive'46'constructor_1515
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base.nonNegative
d_nonNegative_186 ::
  T_ℚ'7512'_8 ->
  T__'8804'__38 -> MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_nonNegative_186 v0 v1
  = case coe v0 of
      C_mkℚ'7512'_22 v2 v3
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Data.Integer.Base.C_NonNegative'46'constructor_1457
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base.-_
d_'45'__190 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8
d_'45'__190 v0
  = case coe v0 of
      C_mkℚ'7512'_22 v1 v2
        -> coe
             C_mkℚ'7512'_22
             (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v1)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base._+_
d__'43'__196 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> T_ℚ'7512'_8
d__'43'__196 v0 v1
  = case coe v0 of
      C_mkℚ'7512'_22 v2 v3
        -> case coe v1 of
             C_mkℚ'7512'_22 v4 v5
               -> coe
                    du__'47'__102
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'43'__276
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2)
                          (coe d_denominator_20 (coe v1)))
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v4)
                          (coe d_denominator_20 (coe v0))))
                    (coe
                       mulInt (coe d_denominatorℕ_18 (coe v0))
                       (coe d_denominatorℕ_18 (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base._*_
d__'42'__202 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> T_ℚ'7512'_8
d__'42'__202 v0 v1
  = case coe v0 of
      C_mkℚ'7512'_22 v2 v3
        -> case coe v1 of
             C_mkℚ'7512'_22 v4 v5
               -> coe
                    du__'47'__102
                    (coe MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2) (coe v4))
                    (coe
                       mulInt (coe d_denominatorℕ_18 (coe v0))
                       (coe d_denominatorℕ_18 (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base._-_
d__'45'__208 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> T_ℚ'7512'_8
d__'45'__208 v0 v1
  = coe d__'43'__196 (coe v0) (coe d_'45'__190 (coe v1))
-- Data.Rational.Unnormalised.Base.1/_
d_1'47'__218 ::
  T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_ℚ'7512'_8
d_1'47'__218 v0 ~v1 = du_1'47'__218 v0
du_1'47'__218 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8
du_1'47'__218 v0
  = case coe v0 of
      C_mkℚ'7512'_22 v1 v2
        -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                 let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                 coe
                   (coe
                      C_mkℚ'7512'_22 (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v3))
             _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                  coe
                    (coe
                       C_mkℚ'7512'_22 (coe subInt (coe (-1 :: Integer)) (coe v2))
                       (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base._÷_
d__'247'__234 ::
  T_ℚ'7512'_8 ->
  T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_ℚ'7512'_8
d__'247'__234 v0 v1 ~v2 = du__'247'__234 v0 v1
du__'247'__234 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> T_ℚ'7512'_8
du__'247'__234 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe d__'42'__202 (coe v0) (coe du_1'47'__218 (coe v1))))
-- Data.Rational.Unnormalised.Base._⊔_
d__'8852'__244 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> T_ℚ'7512'_8
d__'8852'__244 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe d__'8804''7495'__90 (coe v0) (coe v1)) (coe v1) (coe v0)))
-- Data.Rational.Unnormalised.Base._⊓_
d__'8851'__254 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> T_ℚ'7512'_8
d__'8851'__254 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
            (coe d__'8804''7495'__90 (coe v0) (coe v1)) (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Base.∣_∣
d_'8739'_'8739'_260 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8
d_'8739'_'8739'_260 v0
  = case coe v0 of
      C_mkℚ'7512'_22 v1 v2
        -> coe
             C_mkℚ'7512'_22
             (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base.floor
d_floor_266 :: T_ℚ'7512'_8 -> Integer
d_floor_266 v0
  = case coe v0 of
      C_mkℚ'7512'_22 v1 v2
        -> coe
             MAlonzo.Code.Data.Integer.Base.du__'47'__394 (coe v1)
             (coe d_denominator_20 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Base.ceiling
d_ceiling_270 :: T_ℚ'7512'_8 -> Integer
d_ceiling_270 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.d_'45'__252
         (coe d_floor_266 (coe d_'45'__190 (coe v0))))
-- Data.Rational.Unnormalised.Base.truncate
d_truncate_274 :: T_ℚ'7512'_8 -> Integer
d_truncate_274 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d__'8804''7495'__90 (coe v0) (coe d_0ℚ'7512'_108))
      (coe d_ceiling_270 (coe v0)) (coe d_floor_266 (coe v0))
-- Data.Rational.Unnormalised.Base.round
d_round_278 :: T_ℚ'7512'_8 -> Integer
d_round_278 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d__'8804''7495'__90 (coe v0) (coe d_0ℚ'7512'_108))
      (coe d_ceiling_270 (coe d__'45'__208 (coe v0) (coe d_'189'_112)))
      (coe d_floor_266 (coe d__'43'__196 (coe v0) (coe d_'189'_112)))
-- Data.Rational.Unnormalised.Base.fracPart
d_fracPart_282 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8
d_fracPart_282 v0
  = coe
      seq (coe v0)
      (coe
         d_'8739'_'8739'_260
         (coe
            d__'45'__208 (coe v0)
            (coe
               du__'47'__102 (coe d_truncate_274 (coe v0)) (coe (1 :: Integer)))))
-- Data.Rational.Unnormalised.Base.+-rawMagma
d_'43''45'rawMagma_286 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'43''45'rawMagma_286
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_487
      d__'43'__196
-- Data.Rational.Unnormalised.Base.+-0-rawMonoid
d_'43''45'0'45'rawMonoid_288 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'43''45'0'45'rawMonoid_288
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_857
      d__'43'__196 d_0ℚ'7512'_108
-- Data.Rational.Unnormalised.Base.+-0-rawGroup
d_'43''45'0'45'rawGroup_290 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_102
d_'43''45'0'45'rawGroup_290
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawGroup'46'constructor_1319
      d__'43'__196 d_0ℚ'7512'_108 d_'45'__190
-- Data.Rational.Unnormalised.Base.+-*-rawNearSemiring
d_'43''45''42''45'rawNearSemiring_292 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_140
d_'43''45''42''45'rawNearSemiring_292
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawNearSemiring'46'constructor_1841
      d__'43'__196 d__'42'__202 d_0ℚ'7512'_108
-- Data.Rational.Unnormalised.Base.+-*-rawSemiring
d_'43''45''42''45'rawSemiring_294 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_180
d_'43''45''42''45'rawSemiring_294
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawSemiring'46'constructor_2465
      d__'43'__196 d__'42'__202 d_0ℚ'7512'_108 d_1ℚ'7512'_110
-- Data.Rational.Unnormalised.Base.+-*-rawRing
d_'43''45''42''45'rawRing_296 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276
d_'43''45''42''45'rawRing_296
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawRing'46'constructor_3989
      d__'43'__196 d__'42'__202 d_'45'__190 d_0ℚ'7512'_108 d_1ℚ'7512'_110
-- Data.Rational.Unnormalised.Base.*-rawMagma
d_'42''45'rawMagma_298 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'42''45'rawMagma_298
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_487
      d__'42'__202
-- Data.Rational.Unnormalised.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_300 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'42''45'1'45'rawMonoid_300
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_857
      d__'42'__202 d_1ℚ'7512'_110
-- Data.Rational.Unnormalised.Base.+-rawMonoid
d_'43''45'rawMonoid_302 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'43''45'rawMonoid_302 = coe d_'43''45'0'45'rawMonoid_288
-- Data.Rational.Unnormalised.Base.*-rawMonoid
d_'42''45'rawMonoid_304 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'42''45'rawMonoid_304 = coe d_'42''45'1'45'rawMonoid_300
-- Data.Rational.Unnormalised.Base._≠_
d__'8800'__306 :: T_ℚ'7512'_8 -> T_ℚ'7512'_8 -> ()
d__'8800'__306 = erased
