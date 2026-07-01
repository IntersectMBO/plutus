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

module MAlonzo.Code.Data.Integer.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core

-- Data.Integer.Base.0ℤ
d_0ℤ_12 :: Integer
d_0ℤ_12 = coe (0 :: Integer)
-- Data.Integer.Base.-1ℤ
d_'45'1ℤ_14 :: Integer
d_'45'1ℤ_14 = coe (-1 :: Integer)
-- Data.Integer.Base.1ℤ
d_1ℤ_16 :: Integer
d_1ℤ_16 = coe (1 :: Integer)
-- Data.Integer.Base.∣_∣
d_'8739'_'8739'_18 :: Integer -> Integer
d_'8739'_'8739'_18 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe v0
      _ -> coe subInt (coe (0 :: Integer)) (coe v0)
-- Data.Integer.Base.sign
d_sign_24 :: Integer -> MAlonzo.Code.Data.Sign.Base.T_Sign_6
d_sign_24 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Data.Sign.Base.C_'43'_10
      _ -> coe MAlonzo.Code.Data.Sign.Base.C_'45'_8
-- Data.Integer.Base._≤_
d__'8804'__26 a0 a1 = ()
data T__'8804'__26
  = C_'45''8804''45'_34 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_'45''8804''43'_40 |
    C_'43''8804''43'_48 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Data.Integer.Base._<_
d__'60'__50 a0 a1 = ()
data T__'60'__50
  = C_'45''60''45'_58 MAlonzo.Code.Data.Nat.Base.T__'8804'__22 |
    C_'45''60''43'_64 |
    C_'43''60''43'_72 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Data.Integer.Base._≥_
d__'8805'__74 :: Integer -> Integer -> ()
d__'8805'__74 = erased
-- Data.Integer.Base._>_
d__'62'__80 :: Integer -> Integer -> ()
d__'62'__80 = erased
-- Data.Integer.Base._≰_
d__'8816'__86 :: Integer -> Integer -> ()
d__'8816'__86 = erased
-- Data.Integer.Base._≱_
d__'8817'__92 :: Integer -> Integer -> ()
d__'8817'__92 = erased
-- Data.Integer.Base._≮_
d__'8814'__98 :: Integer -> Integer -> ()
d__'8814'__98 = erased
-- Data.Integer.Base._≯_
d__'8815'__104 :: Integer -> Integer -> ()
d__'8815'__104 = erased
-- Data.Integer.Base._≤ᵇ_
d__'8804''7495'__110 :: Integer -> Integer -> Bool
d__'8804''7495'__110 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe
                  MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0) (coe v1)
            _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                    coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v3) (coe v2)))
-- Data.Integer.Base.NonZero
d_NonZero_128 :: Integer -> ()
d_NonZero_128 = erased
-- Data.Integer.Base.Positive
d_Positive_134 a0 = ()
newtype T_Positive_134 = C_constructor_142 AgdaAny
-- Data.Integer.Base.Positive.pos
d_pos_140 :: T_Positive_134 -> AgdaAny
d_pos_140 v0
  = case coe v0 of
      C_constructor_142 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Base.NonNegative
d_NonNegative_146 a0 = ()
newtype T_NonNegative_146 = C_constructor_154 AgdaAny
-- Data.Integer.Base.NonNegative.nonNeg
d_nonNeg_152 :: T_NonNegative_146 -> AgdaAny
d_nonNeg_152 v0
  = case coe v0 of
      C_constructor_154 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Base.NonPositive
d_NonPositive_158 a0 = ()
newtype T_NonPositive_158 = C_constructor_166 AgdaAny
-- Data.Integer.Base.NonPositive.nonPos
d_nonPos_164 :: T_NonPositive_158 -> AgdaAny
d_nonPos_164 v0
  = case coe v0 of
      C_constructor_166 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Base.Negative
d_Negative_170 a0 = ()
newtype T_Negative_170 = C_constructor_178 AgdaAny
-- Data.Integer.Base.Negative.neg
d_neg_176 :: T_Negative_170 -> AgdaAny
d_neg_176 v0
  = case coe v0 of
      C_constructor_178 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Base.pos
d_pos_182 :: Integer -> T_Positive_134
d_pos_182 ~v0 = du_pos_182
du_pos_182 :: T_Positive_134
du_pos_182
  = coe C_constructor_142 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Integer.Base.nonNeg
d_nonNeg_186 :: Integer -> T_NonNegative_146
d_nonNeg_186 ~v0 = du_nonNeg_186
du_nonNeg_186 :: T_NonNegative_146
du_nonNeg_186
  = coe C_constructor_154 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Integer.Base.nonPos0
d_nonPos0_188 :: T_NonPositive_158
d_nonPos0_188
  = coe C_constructor_166 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Integer.Base.nonPos
d_nonPos_192 :: Integer -> T_NonPositive_158
d_nonPos_192 ~v0 = du_nonPos_192
du_nonPos_192 :: T_NonPositive_158
du_nonPos_192
  = coe C_constructor_166 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Integer.Base.neg
d_neg_196 :: Integer -> T_Negative_170
d_neg_196 ~v0 = du_neg_196
du_neg_196 :: T_Negative_170
du_neg_196
  = coe C_constructor_178 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Integer.Base.≢-nonZero
d_'8802''45'nonZero_200 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'8802''45'nonZero_200 v0 ~v1 = du_'8802''45'nonZero_200 v0
du_'8802''45'nonZero_200 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_'8802''45'nonZero_200 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          coe
            MAlonzo.Code.Data.Nat.Base.C_constructor_120
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> coe
             MAlonzo.Code.Data.Nat.Base.C_constructor_120
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Integer.Base.>-nonZero
d_'62''45'nonZero_210 ::
  Integer -> T__'60'__50 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'62''45'nonZero_210 ~v0 v1 = du_'62''45'nonZero_210 v1
du_'62''45'nonZero_210 ::
  T__'60'__50 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_'62''45'nonZero_210 v0
  = case coe v0 of
      C_'43''60''43'_72 v3
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_constructor_120
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Base.<-nonZero
d_'60''45'nonZero_216 ::
  Integer -> T__'60'__50 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_'60''45'nonZero_216 ~v0 v1 = du_'60''45'nonZero_216 v1
du_'60''45'nonZero_216 ::
  T__'60'__50 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_'60''45'nonZero_216 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_constructor_120
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Integer.Base.positive
d_positive_220 :: Integer -> T__'60'__50 -> T_Positive_134
d_positive_220 ~v0 v1 = du_positive_220 v1
du_positive_220 :: T__'60'__50 -> T_Positive_134
du_positive_220 v0
  = case coe v0 of
      C_'43''60''43'_72 v3
        -> coe
             seq (coe v3)
             (coe C_constructor_142 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Base.negative
d_negative_226 :: Integer -> T__'60'__50 -> T_Negative_170
d_negative_226 ~v0 v1 = du_negative_226 v1
du_negative_226 :: T__'60'__50 -> T_Negative_170
du_negative_226 v0
  = coe
      seq (coe v0)
      (coe C_constructor_178 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Integer.Base.nonPositive
d_nonPositive_230 :: Integer -> T__'8804'__26 -> T_NonPositive_158
d_nonPositive_230 ~v0 v1 = du_nonPositive_230 v1
du_nonPositive_230 :: T__'8804'__26 -> T_NonPositive_158
du_nonPositive_230 v0
  = case coe v0 of
      C_'45''8804''43'_40
        -> coe
             C_constructor_166 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      C_'43''8804''43'_48 v3
        -> coe
             seq (coe v3)
             (coe C_constructor_166 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Base.nonNegative
d_nonNegative_234 :: Integer -> T__'8804'__26 -> T_NonNegative_146
d_nonNegative_234 v0 ~v1 = du_nonNegative_234 v0
du_nonNegative_234 :: Integer -> T_NonNegative_146
du_nonNegative_234 v0
  = coe
      seq (coe v0)
      (coe C_constructor_154 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Integer.Base._◃_
d__'9667'__238 ::
  MAlonzo.Code.Data.Sign.Base.T_Sign_6 -> Integer -> Integer
d__'9667'__238 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> case coe v0 of
             MAlonzo.Code.Data.Sign.Base.C_'45'_8
               -> coe subInt (coe (0 :: Integer)) (coe v1)
             MAlonzo.Code.Data.Sign.Base.C_'43'_10 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Integer.Base.SignAbs
d_SignAbs_244 a0 = ()
data T_SignAbs_244
  = C__'9666'__250 MAlonzo.Code.Data.Sign.Base.T_Sign_6 Integer
-- Data.Integer.Base.signAbs
d_signAbs_254 :: Integer -> T_SignAbs_244
d_signAbs_254 v0
  = case coe v0 of
      0 -> coe
             C__'9666'__250 (coe MAlonzo.Code.Data.Sign.Base.C_'43'_10)
             (coe (0 :: Integer))
      _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
          coe
            C__'9666'__250 (coe MAlonzo.Code.Data.Sign.Base.C_'43'_10) (coe v0)
      _ -> coe
             C__'9666'__250 (coe MAlonzo.Code.Data.Sign.Base.C_'45'_8)
             (coe subInt (coe (0 :: Integer)) (coe v0))
-- Data.Integer.Base.-_
d_'45'__260 :: Integer -> Integer
d_'45'__260 v0 = coe subInt (coe (0 :: Integer)) (coe v0)
-- Data.Integer.Base._⊖_
d__'8854'__266 :: Integer -> Integer -> Integer
d__'8854'__266 v0 v1
  = let v2 = ltInt (coe v0) (coe v1) in
    coe
      (if coe v2
         then coe d_'45'__260 (coe subInt (coe v1) (coe v0))
         else coe subInt (coe v0) (coe v1))
-- Data.Integer.Base._+_
d__'43'__284 :: Integer -> Integer -> Integer
d__'43'__284 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe addInt (coe v0) (coe v1)
            _ -> coe
                   d__'8854'__266 (coe v0) (coe subInt (coe (0 :: Integer)) (coe v1))
      _ -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe
                   d__'8854'__266 (coe v1) (coe subInt (coe (0 :: Integer)) (coe v0))
             _ -> coe addInt (coe v0) (coe v1)
-- Data.Integer.Base._-_
d__'45'__302 :: Integer -> Integer -> Integer
d__'45'__302 v0 v1
  = coe d__'43'__284 (coe v0) (coe d_'45'__260 (coe v1))
-- Data.Integer.Base.suc
d_suc_308 :: Integer -> Integer
d_suc_308 v0 = coe d__'43'__284 (coe d_1ℤ_16) (coe v0)
-- Data.Integer.Base.pred
d_pred_312 :: Integer -> Integer
d_pred_312 v0 = coe d__'43'__284 (coe d_'45'1ℤ_14) (coe v0)
-- Data.Integer.Base._*_
d__'42'__316 :: Integer -> Integer -> Integer
d__'42'__316 v0 v1
  = coe
      d__'9667'__238
      (coe
         MAlonzo.Code.Data.Sign.Base.d__'42'__14 (coe d_sign_24 (coe v0))
         (coe d_sign_24 (coe v1)))
      (coe
         mulInt (coe d_'8739'_'8739'_18 (coe v0))
         (coe d_'8739'_'8739'_18 (coe v1)))
-- Data.Integer.Base._^_
d__'94'__322 :: Integer -> Integer -> Integer
d__'94'__322 v0 v1
  = case coe v1 of
      0 -> coe d_1ℤ_16
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe d__'42'__316 (coe v0) (coe d__'94'__322 (coe v0) (coe v2)))
-- Data.Integer.Base._⊔_
d__'8852'__330 :: Integer -> Integer -> Integer
d__'8852'__330 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v1)
            _ -> coe v0
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) -> coe v1
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          subInt (coe (-1 :: Integer))
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8851'__236 (coe v2) (coe v3))))
-- Data.Integer.Base._⊓_
d__'8851'__348 :: Integer -> Integer -> Integer
d__'8851'__348 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          case coe v1 of
            _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                coe MAlonzo.Code.Data.Nat.Base.d__'8851'__236 (coe v0) (coe v1)
            _ -> coe v1
      _ -> let v2 = subInt (coe (-1 :: Integer)) (coe v0) in
           coe
             (case coe v1 of
                _ | coe geqInt (coe v1) (coe (0 :: Integer)) -> coe v0
                _ -> let v3 = subInt (coe (-1 :: Integer)) (coe v1) in
                     coe
                       (coe
                          subInt (coe (-1 :: Integer))
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v2) (coe v3))))
-- Data.Integer.Base._/ℕ_
d__'47'ℕ__372 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__'47'ℕ__372 v0 v1 ~v2 = du__'47'ℕ__372 v0 v1
du__'47'ℕ__372 :: Integer -> Integer -> Integer
du__'47'ℕ__372 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1)
      _ -> let v2
                 = coe
                     MAlonzo.Code.Data.Nat.Base.du__'37'__330
                     (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1) in
           coe
             (case coe v2 of
                0 -> coe
                       d_'45'__260
                       (coe
                          MAlonzo.Code.Data.Nat.Base.du__'47'__318
                          (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1))
                _ -> coe
                       subInt (coe (-1 :: Integer))
                       (coe
                          MAlonzo.Code.Data.Nat.Base.du__'47'__318
                          (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1)))
-- Data.Integer.Base._/_
d__'47'__402 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__'47'__402 v0 v1 ~v2 = du__'47'__402 v0 v1
du__'47'__402 :: Integer -> Integer -> Integer
du__'47'__402 v0 v1
  = coe
      d__'42'__316
      (coe d__'9667'__238 (coe d_sign_24 (coe v1)) (coe (1 :: Integer)))
      (coe du__'47'ℕ__372 (coe v0) (coe d_'8739'_'8739'_18 (coe v1)))
-- Data.Integer.Base._%ℕ_
d__'37'ℕ__414 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__'37'ℕ__414 v0 v1 ~v2 = du__'37'ℕ__414 v0 v1
du__'37'ℕ__414 :: Integer -> Integer -> Integer
du__'37'ℕ__414 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v0) (coe v1)
      _ -> let v2
                 = coe
                     MAlonzo.Code.Data.Nat.Base.du__'37'__330
                     (coe subInt (coe (0 :: Integer)) (coe v0)) (coe v1) in
           coe
             (case coe v2 of
                0 -> coe (0 :: Integer)
                _ -> coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v2)
-- Data.Integer.Base._%_
d__'37'__444 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer
d__'37'__444 v0 v1 ~v2 = du__'37'__444 v0 v1
du__'37'__444 :: Integer -> Integer -> Integer
du__'37'__444 v0 v1
  = coe du__'37'ℕ__414 (coe v0) (coe d_'8739'_'8739'_18 (coe v1))
-- Data.Integer.Base.+-rawMagma
d_'43''45'rawMagma_450 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'43''45'rawMagma_450
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_68 d__'43'__284
-- Data.Integer.Base.+-0-rawMonoid
d_'43''45'0'45'rawMonoid_452 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74
d_'43''45'0'45'rawMonoid_452
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_102 d__'43'__284
      d_0ℤ_12
-- Data.Integer.Base.+-0-rawGroup
d_'43''45'0'45'rawGroup_454 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108
d_'43''45'0'45'rawGroup_454
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_142 d__'43'__284
      d_0ℤ_12 d_'45'__260
-- Data.Integer.Base.*-rawMagma
d_'42''45'rawMagma_456 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'42''45'rawMagma_456
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_68 d__'42'__316
-- Data.Integer.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_458 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74
d_'42''45'1'45'rawMonoid_458
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_102 d__'42'__316
      d_1ℤ_16
-- Data.Integer.Base.+-*-rawNearSemiring
d_'43''45''42''45'rawNearSemiring_460 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148
d_'43''45''42''45'rawNearSemiring_460
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_184 d__'43'__284
      d__'42'__316 d_0ℤ_12
-- Data.Integer.Base.+-*-rawSemiring
d_'43''45''42''45'rawSemiring_462 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190
d_'43''45''42''45'rawSemiring_462
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_234 d__'43'__284
      d__'42'__316 d_0ℤ_12 d_1ℤ_16
-- Data.Integer.Base.+-*-rawRing
d_'43''45''42''45'rawRing_464 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_290
d_'43''45''42''45'rawRing_464
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_344 d__'43'__284
      d__'42'__316 d_'45'__260 d_0ℤ_12 d_1ℤ_16
