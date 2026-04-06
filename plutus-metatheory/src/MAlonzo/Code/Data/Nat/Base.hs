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

module MAlonzo.Code.Data.Nat.Base where

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
import qualified MAlonzo.Code.Algebra.Definitions.RawMagma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Parity.Base
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core

-- Data.Nat.Base._≤ᵇ_
d__'8804''7495'__14 :: Integer -> Integer -> Bool
d__'8804''7495'__14 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe ltInt (coe v2) (coe v1))
-- Data.Nat.Base._≤_
d__'8804'__22 a0 a1 = ()
data T__'8804'__22 = C_z'8804'n_26 | C_s'8804's_34 T__'8804'__22
-- Data.Nat.Base._<_
d__'60'__36 :: Integer -> Integer -> ()
d__'60'__36 = erased
-- Data.Nat.Base.s≤s⁻¹
d_s'8804's'8315''185'_62 ::
  Integer -> Integer -> T__'8804'__22 -> T__'8804'__22
d_s'8804's'8315''185'_62 ~v0 ~v1 v2 = du_s'8804's'8315''185'_62 v2
du_s'8804's'8315''185'_62 :: T__'8804'__22 -> T__'8804'__22
du_s'8804's'8315''185'_62 v0
  = case coe v0 of
      C_s'8804's_34 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.s<s⁻¹
d_s'60's'8315''185'_70 ::
  Integer -> Integer -> T__'8804'__22 -> T__'8804'__22
d_s'60's'8315''185'_70 ~v0 ~v1 v2 = du_s'60's'8315''185'_70 v2
du_s'60's'8315''185'_70 :: T__'8804'__22 -> T__'8804'__22
du_s'60's'8315''185'_70 v0
  = case coe v0 of
      C_s'8804's_34 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base._≥_
d__'8805'__74 :: Integer -> Integer -> ()
d__'8805'__74 = erased
-- Data.Nat.Base._>_
d__'62'__80 :: Integer -> Integer -> ()
d__'62'__80 = erased
-- Data.Nat.Base._≰_
d__'8816'__86 :: Integer -> Integer -> ()
d__'8816'__86 = erased
-- Data.Nat.Base._≮_
d__'8814'__92 :: Integer -> Integer -> ()
d__'8814'__92 = erased
-- Data.Nat.Base._≱_
d__'8817'__98 :: Integer -> Integer -> ()
d__'8817'__98 = erased
-- Data.Nat.Base._≯_
d__'8815'__104 :: Integer -> Integer -> ()
d__'8815'__104 = erased
-- Data.Nat.Base.NonZero
d_NonZero_112 a0 = ()
newtype T_NonZero_112 = C_constructor_120 AgdaAny
-- Data.Nat.Base.NonZero.nonZero
d_nonZero_118 :: T_NonZero_112 -> AgdaAny
d_nonZero_118 v0
  = case coe v0 of
      C_constructor_120 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.nonZero
d_nonZero_124 :: Integer -> T_NonZero_112
d_nonZero_124 ~v0 = du_nonZero_124
du_nonZero_124 :: T_NonZero_112
du_nonZero_124
  = coe C_constructor_120 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Base.≢-nonZero
d_'8802''45'nonZero_128 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_NonZero_112
d_'8802''45'nonZero_128 v0 ~v1 = du_'8802''45'nonZero_128 v0
du_'8802''45'nonZero_128 :: Integer -> T_NonZero_112
du_'8802''45'nonZero_128 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> coe
             C_constructor_120 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Base.>-nonZero
d_'62''45'nonZero_138 :: Integer -> T__'8804'__22 -> T_NonZero_112
d_'62''45'nonZero_138 ~v0 v1 = du_'62''45'nonZero_138 v1
du_'62''45'nonZero_138 :: T__'8804'__22 -> T_NonZero_112
du_'62''45'nonZero_138 v0
  = case coe v0 of
      C_s'8804's_34 v3
        -> coe
             seq (coe v3)
             (coe C_constructor_120 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.≢-nonZero⁻¹
d_'8802''45'nonZero'8315''185'_142 ::
  Integer ->
  T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8802''45'nonZero'8315''185'_142 = erased
-- Data.Nat.Base.>-nonZero⁻¹
d_'62''45'nonZero'8315''185'_148 ::
  Integer -> T_NonZero_112 -> T__'8804'__22
d_'62''45'nonZero'8315''185'_148 ~v0 ~v1
  = du_'62''45'nonZero'8315''185'_148
du_'62''45'nonZero'8315''185'_148 :: T__'8804'__22
du_'62''45'nonZero'8315''185'_148
  = coe C_s'8804's_34 (coe C_z'8804'n_26)
-- Data.Nat.Base.NonTrivial
d_NonTrivial_154 a0 = ()
newtype T_NonTrivial_154 = C_constructor_162 AgdaAny
-- Data.Nat.Base.NonTrivial.nonTrivial
d_nonTrivial_160 :: T_NonTrivial_154 -> AgdaAny
d_nonTrivial_160 v0
  = case coe v0 of
      C_constructor_162 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.nonTrivial
d_nonTrivial_166 :: Integer -> T_NonTrivial_154
d_nonTrivial_166 ~v0 = du_nonTrivial_166
du_nonTrivial_166 :: T_NonTrivial_154
du_nonTrivial_166
  = coe C_constructor_162 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Base.n>1⇒nonTrivial
d_n'62'1'8658'nonTrivial_170 ::
  Integer -> T__'8804'__22 -> T_NonTrivial_154
d_n'62'1'8658'nonTrivial_170 ~v0 v1
  = du_n'62'1'8658'nonTrivial_170 v1
du_n'62'1'8658'nonTrivial_170 :: T__'8804'__22 -> T_NonTrivial_154
du_n'62'1'8658'nonTrivial_170 v0
  = case coe v0 of
      C_s'8804's_34 v3
        -> case coe v3 of
             C_s'8804's_34 v6
               -> coe
                    seq (coe v6)
                    (coe C_constructor_162 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.nonTrivial⇒nonZero
d_nonTrivial'8658'nonZero_174 ::
  Integer -> T_NonTrivial_154 -> T_NonZero_112
d_nonTrivial'8658'nonZero_174 ~v0 ~v1
  = du_nonTrivial'8658'nonZero_174
du_nonTrivial'8658'nonZero_174 :: T_NonZero_112
du_nonTrivial'8658'nonZero_174
  = coe C_constructor_120 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Base.nonTrivial⇒n>1
d_nonTrivial'8658'n'62'1_178 ::
  Integer -> T_NonTrivial_154 -> T__'8804'__22
d_nonTrivial'8658'n'62'1_178 ~v0 ~v1
  = du_nonTrivial'8658'n'62'1_178
du_nonTrivial'8658'n'62'1_178 :: T__'8804'__22
du_nonTrivial'8658'n'62'1_178
  = coe C_s'8804's_34 (coe C_s'8804's_34 (coe C_z'8804'n_26))
-- Data.Nat.Base.nonTrivial⇒≢1
d_nonTrivial'8658''8802'1_182 ::
  Integer ->
  T_NonTrivial_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nonTrivial'8658''8802'1_182 = erased
-- Data.Nat.Base.+-rawMagma
d_'43''45'rawMagma_184 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'43''45'rawMagma_184
  = coe MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_68 addInt
-- Data.Nat.Base.+-0-rawMonoid
d_'43''45'0'45'rawMonoid_186 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74
d_'43''45'0'45'rawMonoid_186
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_102 addInt
      (0 :: Integer)
-- Data.Nat.Base.*-rawMagma
d_'42''45'rawMagma_188 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'42''45'rawMagma_188
  = coe MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_68 mulInt
-- Data.Nat.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_190 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74
d_'42''45'1'45'rawMonoid_190
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_102 mulInt
      (1 :: Integer)
-- Data.Nat.Base.+-*-rawNearSemiring
d_'43''45''42''45'rawNearSemiring_192 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_148
d_'43''45''42''45'rawNearSemiring_192
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_184 addInt mulInt
      (0 :: Integer)
-- Data.Nat.Base.+-*-rawSemiring
d_'43''45''42''45'rawSemiring_194 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_190
d_'43''45''42''45'rawSemiring_194
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_234 addInt mulInt
      (0 :: Integer) (1 :: Integer)
-- Data.Nat.Base.pred
d_pred_196 :: Integer -> Integer
d_pred_196 v0
  = coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer)
-- Data.Nat.Base._+⋎_
d__'43''8910'__200 :: Integer -> Integer -> Integer
d__'43''8910'__200 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                addInt (coe (1 :: Integer))
                (coe d__'43''8910'__200 (coe v1) (coe v2)))
-- Data.Nat.Base._⊔_
d__'8852'__208 :: Integer -> Integer -> Integer
d__'8852'__208 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe v0
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe d__'8852'__208 (coe v2) (coe v3))))
-- Data.Nat.Base._⊔′_
d__'8852''8242'__218 :: Integer -> Integer -> Integer
d__'8852''8242'__218 v0 v1
  = let v2 = ltInt (coe v0) (coe v1) in
    coe (if coe v2 then coe v1 else coe v0)
-- Data.Nat.Base._⊓_
d__'8851'__236 :: Integer -> Integer -> Integer
d__'8851'__236 v0 v1
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe (0 :: Integer)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe d__'8851'__236 (coe v2) (coe v3))))
-- Data.Nat.Base._⊓′_
d__'8851''8242'__246 :: Integer -> Integer -> Integer
d__'8851''8242'__246 v0 v1
  = let v2 = ltInt (coe v0) (coe v1) in
    coe (if coe v2 then coe v0 else coe v1)
-- Data.Nat.Base.parity
d_parity_264 :: Integer -> MAlonzo.Code.Data.Parity.Base.T_Parity_6
d_parity_264 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Parity.Base.C_0ℙ_8
      1 -> coe MAlonzo.Code.Data.Parity.Base.C_1ℙ_10
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe (coe d_parity_264 (coe v1))
-- Data.Nat.Base.⌊_/2⌋
d_'8970'_'47'2'8971'_268 :: Integer -> Integer
d_'8970'_'47'2'8971'_268 v0
  = case coe v0 of
      0 -> coe (0 :: Integer)
      1 -> coe (0 :: Integer)
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                addInt (coe (1 :: Integer))
                (coe d_'8970'_'47'2'8971'_268 (coe v1)))
-- Data.Nat.Base.⌈_/2⌉
d_'8968'_'47'2'8969'_272 :: Integer -> Integer
d_'8968'_'47'2'8969'_272 v0
  = coe
      d_'8970'_'47'2'8971'_268 (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Base._^_
d__'94'__276 :: Integer -> Integer -> Integer
d__'94'__276 v0 v1
  = case coe v1 of
      0 -> coe (1 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe (coe mulInt (coe v0) (coe d__'94'__276 (coe v0) (coe v2)))
-- Data.Nat.Base.∣_-_∣
d_'8739'_'45'_'8739'_284 :: Integer -> Integer -> Integer
d_'8739'_'45'_'8739'_284 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe v0
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d_'8739'_'45'_'8739'_284 (coe v2) (coe v3)))
-- Data.Nat.Base.∣_-_∣′
d_'8739'_'45'_'8739''8242'_294 :: Integer -> Integer -> Integer
d_'8739'_'45'_'8739''8242'_294 v0 v1
  = let v2 = ltInt (coe v0) (coe v1) in
    coe
      (if coe v2
         then coe subInt (coe v1) (coe v0)
         else coe subInt (coe v0) (coe v1))
-- Data.Nat.Base._/_
d__'47'__318 :: Integer -> Integer -> T_NonZero_112 -> Integer
d__'47'__318 v0 v1 ~v2 = du__'47'__318 v0 v1
du__'47'__318 :: Integer -> Integer -> Integer
du__'47'__318 v0 v1 = coe quotInt (coe v0) (coe v1)
-- Data.Nat.Base._%_
d__'37'__330 :: Integer -> Integer -> T_NonZero_112 -> Integer
d__'37'__330 v0 v1 ~v2 = du__'37'__330 v0 v1
du__'37'__330 :: Integer -> Integer -> Integer
du__'37'__330 v0 v1 = coe remInt (coe v0) (coe v1)
-- Data.Nat.Base._!
d__'33'_336 :: Integer -> Integer
d__'33'_336 v0
  = case coe v0 of
      0 -> coe (1 :: Integer)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe mulInt (coe v0) (coe d__'33'_336 (coe v1)))
-- Data.Nat.Base._≤′_
d__'8804''8242'__342 a0 a1 = ()
data T__'8804''8242'__342
  = C_'8804''8242''45'reflexive_348 |
    C_'8804''8242''45'step_352 T__'8804''8242'__342
-- Data.Nat.Base._<′_
d__'60''8242'__358 :: Integer -> Integer -> ()
d__'60''8242'__358 = erased
-- Data.Nat.Base._≥′_
d__'8805''8242'__372 :: Integer -> Integer -> ()
d__'8805''8242'__372 = erased
-- Data.Nat.Base._>′_
d__'62''8242'__378 :: Integer -> Integer -> ()
d__'62''8242'__378 = erased
-- Data.Nat.Base._≤″_
d__'8804''8243'__388 :: Integer -> Integer -> ()
d__'8804''8243'__388 = erased
-- Data.Nat.Base._<″_
d__'60''8243'__390 :: Integer -> Integer -> ()
d__'60''8243'__390 = erased
-- Data.Nat.Base._≥″_
d__'8805''8243'__396 :: Integer -> Integer -> ()
d__'8805''8243'__396 = erased
-- Data.Nat.Base._>″_
d__'62''8243'__402 :: Integer -> Integer -> ()
d__'62''8243'__402 = erased
-- Data.Nat.Base.s<″s⁻¹
d_s'60''8243's'8315''185'_412 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
d_s'60''8243's'8315''185'_412 ~v0 ~v1 v2
  = du_s'60''8243's'8315''185'_412 v2
du_s'60''8243's'8315''185'_412 ::
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
du_s'60''8243's'8315''185'_412 v0 = coe v0
-- Data.Nat.Base._≤‴_
d__'8804''8244'__422 a0 a1 = ()
data T__'8804''8244'__422
  = C_'8804''8244''45'reflexive_434 |
    C_'8804''8244''45'step_436 T__'8804''8244'__422
-- Data.Nat.Base._<‴_
d__'60''8244'__424 :: Integer -> Integer -> ()
d__'60''8244'__424 = erased
-- Data.Nat.Base._≥‴_
d__'8805''8244'__440 :: Integer -> Integer -> ()
d__'8805''8244'__440 = erased
-- Data.Nat.Base._>‴_
d__'62''8244'__446 :: Integer -> Integer -> ()
d__'62''8244'__446 = erased
-- Data.Nat.Base.Ordering
d_Ordering_452 a0 a1 = ()
data T_Ordering_452
  = C_less_458 Integer | C_equal_462 | C_greater_468 Integer
-- Data.Nat.Base.compare
d_compare_474 :: Integer -> Integer -> T_Ordering_452
d_compare_474 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe C_equal_462
             _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe C_less_458 v2)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe C_greater_468 v2
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d_compare_474 (coe v2) (coe v3)))
-- Data.Nat.Base.s≤″s⁻¹
d_s'8804''8243's'8315''185'_528 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
d_s'8804''8243's'8315''185'_528 ~v0 ~v1 v2
  = du_s'8804''8243's'8315''185'_528 v2
du_s'8804''8243's'8315''185'_528 ::
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28
du_s'8804''8243's'8315''185'_528 v0 = coe v0
