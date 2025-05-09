{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Data.Nat.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Nat qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.Code.Algebra.Definitions.RawMagma qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Parity.Base qualified
import MAlonzo.Code.Relation.Nullary.Negation.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
      _                -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.s<s⁻¹
d_s'60's'8315''185'_70 ::
  Integer -> Integer -> T__'8804'__22 -> T__'8804'__22
d_s'60's'8315''185'_70 ~v0 ~v1 v2 = du_s'60's'8315''185'_70 v2
du_s'60's'8315''185'_70 :: T__'8804'__22 -> T__'8804'__22
du_s'60's'8315''185'_70 v0
  = case coe v0 of
      C_s'8804's_34 v3 -> coe v3
      _                -> MAlonzo.RTE.mazUnreachableError
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
newtype T_NonZero_112 = C_NonZero'46'constructor_3575 AgdaAny
-- Data.Nat.Base.NonZero.nonZero
d_nonZero_118 :: T_NonZero_112 -> AgdaAny
d_nonZero_118 v0
  = case coe v0 of
      C_NonZero'46'constructor_3575 v1 -> coe v1
      _                                -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.nonZero
d_nonZero_122 :: Integer -> T_NonZero_112
d_nonZero_122 ~v0 = du_nonZero_122
du_nonZero_122 :: T_NonZero_112
du_nonZero_122
  = coe
      C_NonZero'46'constructor_3575
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Base.≢-nonZero
d_'8802''45'nonZero_126 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_NonZero_112
d_'8802''45'nonZero_126 v0 ~v1 = du_'8802''45'nonZero_126 v0
du_'8802''45'nonZero_126 :: Integer -> T_NonZero_112
du_'8802''45'nonZero_126 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> coe
             C_NonZero'46'constructor_3575
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Base.>-nonZero
d_'62''45'nonZero_136 :: Integer -> T__'8804'__22 -> T_NonZero_112
d_'62''45'nonZero_136 ~v0 v1 = du_'62''45'nonZero_136 v1
du_'62''45'nonZero_136 :: T__'8804'__22 -> T_NonZero_112
du_'62''45'nonZero_136 v0
  = case coe v0 of
      C_s'8804's_34 v3
        -> coe
             seq (coe v3)
             (coe
                C_NonZero'46'constructor_3575
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.≢-nonZero⁻¹
d_'8802''45'nonZero'8315''185'_140 ::
  Integer ->
  T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8802''45'nonZero'8315''185'_140 = erased
-- Data.Nat.Base.>-nonZero⁻¹
d_'62''45'nonZero'8315''185'_146 ::
  Integer -> T_NonZero_112 -> T__'8804'__22
d_'62''45'nonZero'8315''185'_146 ~v0 ~v1
  = du_'62''45'nonZero'8315''185'_146
du_'62''45'nonZero'8315''185'_146 :: T__'8804'__22
du_'62''45'nonZero'8315''185'_146
  = coe C_s'8804's_34 (coe C_z'8804'n_26)
-- Data.Nat.Base.NonTrivial
d_NonTrivial_152 a0 = ()
newtype T_NonTrivial_152 = C_NonTrivial'46'constructor_5661 AgdaAny
-- Data.Nat.Base.NonTrivial.nonTrivial
d_nonTrivial_158 :: T_NonTrivial_152 -> AgdaAny
d_nonTrivial_158 v0
  = case coe v0 of
      C_NonTrivial'46'constructor_5661 v1 -> coe v1
      _                                   -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.nonTrivial
d_nonTrivial_162 :: Integer -> T_NonTrivial_152
d_nonTrivial_162 ~v0 = du_nonTrivial_162
du_nonTrivial_162 :: T_NonTrivial_152
du_nonTrivial_162
  = coe
      C_NonTrivial'46'constructor_5661
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Base.n>1⇒nonTrivial
d_n'62'1'8658'nonTrivial_166 ::
  Integer -> T__'8804'__22 -> T_NonTrivial_152
d_n'62'1'8658'nonTrivial_166 ~v0 v1
  = du_n'62'1'8658'nonTrivial_166 v1
du_n'62'1'8658'nonTrivial_166 :: T__'8804'__22 -> T_NonTrivial_152
du_n'62'1'8658'nonTrivial_166 v0
  = case coe v0 of
      C_s'8804's_34 v3
        -> case coe v3 of
             C_s'8804's_34 v6
               -> coe
                    seq (coe v6)
                    (coe
                       C_NonTrivial'46'constructor_5661
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Base.nonTrivial⇒nonZero
d_nonTrivial'8658'nonZero_170 ::
  Integer -> T_NonTrivial_152 -> T_NonZero_112
d_nonTrivial'8658'nonZero_170 ~v0 ~v1
  = du_nonTrivial'8658'nonZero_170
du_nonTrivial'8658'nonZero_170 :: T_NonZero_112
du_nonTrivial'8658'nonZero_170
  = coe
      C_NonZero'46'constructor_3575
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Base.nonTrivial⇒n>1
d_nonTrivial'8658'n'62'1_174 ::
  Integer -> T_NonTrivial_152 -> T__'8804'__22
d_nonTrivial'8658'n'62'1_174 ~v0 ~v1
  = du_nonTrivial'8658'n'62'1_174
du_nonTrivial'8658'n'62'1_174 :: T__'8804'__22
du_nonTrivial'8658'n'62'1_174
  = coe C_s'8804's_34 (coe C_s'8804's_34 (coe C_z'8804'n_26))
-- Data.Nat.Base.nonTrivial⇒≢1
d_nonTrivial'8658''8802'1_178 ::
  Integer ->
  T_NonTrivial_152 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nonTrivial'8658''8802'1_178 = erased
-- Data.Nat.Base.+-rawMagma
d_'43''45'rawMagma_180 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'43''45'rawMagma_180
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_341
      addInt
-- Data.Nat.Base.+-0-rawMonoid
d_'43''45'0'45'rawMonoid_182 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64
d_'43''45'0'45'rawMonoid_182
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_745
      addInt (0 :: Integer)
-- Data.Nat.Base.*-rawMagma
d_'42''45'rawMagma_184 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'42''45'rawMagma_184
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_341
      mulInt
-- Data.Nat.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_186 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64
d_'42''45'1'45'rawMonoid_186
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_745
      mulInt (1 :: Integer)
-- Data.Nat.Base.+-*-rawNearSemiring
d_'43''45''42''45'rawNearSemiring_188 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134
d_'43''45''42''45'rawNearSemiring_188
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawNearSemiring'46'constructor_1729
      addInt mulInt (0 :: Integer)
-- Data.Nat.Base.+-*-rawSemiring
d_'43''45''42''45'rawSemiring_190 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174
d_'43''45''42''45'rawSemiring_190
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawSemiring'46'constructor_2353
      addInt mulInt (0 :: Integer) (1 :: Integer)
-- Data.Nat.Base.pred
d_pred_192 :: Integer -> Integer
d_pred_192 v0
  = coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer)
-- Data.Nat.Base._+⋎_
d__'43''8910'__196 :: Integer -> Integer -> Integer
d__'43''8910'__196 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                addInt (coe (1 :: Integer))
                (coe d__'43''8910'__196 (coe v1) (coe v2)))
-- Data.Nat.Base._⊔_
d__'8852'__204 :: Integer -> Integer -> Integer
d__'8852'__204 v0 v1
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
                          (coe d__'8852'__204 (coe v2) (coe v3))))
-- Data.Nat.Base._⊔′_
d__'8852''8242'__214 :: Integer -> Integer -> Integer
d__'8852''8242'__214 v0 v1
  = let v2 = ltInt (coe v0) (coe v1) in
    coe (if coe v2 then coe v1 else coe v0)
-- Data.Nat.Base._⊓_
d__'8851'__232 :: Integer -> Integer -> Integer
d__'8851'__232 v0 v1
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
                          (coe d__'8851'__232 (coe v2) (coe v3))))
-- Data.Nat.Base._⊓′_
d__'8851''8242'__242 :: Integer -> Integer -> Integer
d__'8851''8242'__242 v0 v1
  = let v2 = ltInt (coe v0) (coe v1) in
    coe (if coe v2 then coe v0 else coe v1)
-- Data.Nat.Base.parity
d_parity_260 :: Integer -> MAlonzo.Code.Data.Parity.Base.T_Parity_6
d_parity_260 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Parity.Base.C_0ℙ_8
      1 -> coe MAlonzo.Code.Data.Parity.Base.C_1ℙ_10
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe (coe d_parity_260 (coe v1))
-- Data.Nat.Base.⌊_/2⌋
d_'8970'_'47'2'8971'_264 :: Integer -> Integer
d_'8970'_'47'2'8971'_264 v0
  = case coe v0 of
      0 -> coe (0 :: Integer)
      1 -> coe (0 :: Integer)
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                addInt (coe (1 :: Integer))
                (coe d_'8970'_'47'2'8971'_264 (coe v1)))
-- Data.Nat.Base.⌈_/2⌉
d_'8968'_'47'2'8969'_268 :: Integer -> Integer
d_'8968'_'47'2'8969'_268 v0
  = coe
      d_'8970'_'47'2'8971'_264 (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Base._^_
d__'94'__272 :: Integer -> Integer -> Integer
d__'94'__272 v0 v1
  = case coe v1 of
      0 -> coe (1 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe (coe mulInt (coe v0) (coe d__'94'__272 (coe v0) (coe v2)))
-- Data.Nat.Base.∣_-_∣
d_'8739'_'45'_'8739'_280 :: Integer -> Integer -> Integer
d_'8739'_'45'_'8739'_280 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe v0
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d_'8739'_'45'_'8739'_280 (coe v2) (coe v3)))
-- Data.Nat.Base.∣_-_∣′
d_'8739'_'45'_'8739''8242'_290 :: Integer -> Integer -> Integer
d_'8739'_'45'_'8739''8242'_290 v0 v1
  = let v2 = ltInt (coe v0) (coe v1) in
    coe
      (if coe v2
         then coe subInt (coe v1) (coe v0)
         else coe subInt (coe v0) (coe v1))
-- Data.Nat.Base._/_
d__'47'__314 :: Integer -> Integer -> T_NonZero_112 -> Integer
d__'47'__314 v0 v1 ~v2 = du__'47'__314 v0 v1
du__'47'__314 :: Integer -> Integer -> Integer
du__'47'__314 v0 v1 = coe quotInt (coe v0) (coe v1)
-- Data.Nat.Base._%_
d__'37'__326 :: Integer -> Integer -> T_NonZero_112 -> Integer
d__'37'__326 v0 v1 ~v2 = du__'37'__326 v0 v1
du__'37'__326 :: Integer -> Integer -> Integer
du__'37'__326 v0 v1 = coe remInt (coe v0) (coe v1)
-- Data.Nat.Base._!
d__'33'_332 :: Integer -> Integer
d__'33'_332 v0
  = case coe v0 of
      0 -> coe (1 :: Integer)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe mulInt (coe v0) (coe d__'33'_332 (coe v1)))
-- Data.Nat.Base._≤′_
d__'8804''8242'__338 a0 a1 = ()
data T__'8804''8242'__338
  = C_'8804''8242''45'refl_342 |
    C_'8804''8242''45'step_348 T__'8804''8242'__338
-- Data.Nat.Base._<′_
d__'60''8242'__350 :: Integer -> Integer -> ()
d__'60''8242'__350 = erased
-- Data.Nat.Base._≥′_
d__'8805''8242'__364 :: Integer -> Integer -> ()
d__'8805''8242'__364 = erased
-- Data.Nat.Base._>′_
d__'62''8242'__370 :: Integer -> Integer -> ()
d__'62''8242'__370 = erased
-- Data.Nat.Base._≤″_
d__'8804''8243'__380 :: Integer -> Integer -> ()
d__'8804''8243'__380 = erased
-- Data.Nat.Base._<″_
d__'60''8243'__382 :: Integer -> Integer -> ()
d__'60''8243'__382 = erased
-- Data.Nat.Base._≥″_
d__'8805''8243'__388 :: Integer -> Integer -> ()
d__'8805''8243'__388 = erased
-- Data.Nat.Base._>″_
d__'62''8243'__394 :: Integer -> Integer -> ()
d__'62''8243'__394 = erased
-- Data.Nat.Base.s<″s⁻¹
d_s'60''8243's'8315''185'_404 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
d_s'60''8243's'8315''185'_404 ~v0 ~v1 v2
  = du_s'60''8243's'8315''185'_404 v2
du_s'60''8243's'8315''185'_404 ::
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
du_s'60''8243's'8315''185'_404 v0 = coe v0
-- Data.Nat.Base._≤‴_
d__'8804''8244'__408 a0 a1 = ()
data T__'8804''8244'__408
  = C_'8804''8244''45'refl_412 |
    C_'8804''8244''45'step_418 T__'8804''8244'__408
-- Data.Nat.Base._<‴_
d__'60''8244'__420 :: Integer -> Integer -> ()
d__'60''8244'__420 = erased
-- Data.Nat.Base._≥‴_
d__'8805''8244'__426 :: Integer -> Integer -> ()
d__'8805''8244'__426 = erased
-- Data.Nat.Base._>‴_
d__'62''8244'__432 :: Integer -> Integer -> ()
d__'62''8244'__432 = erased
-- Data.Nat.Base.Ordering
d_Ordering_438 a0 a1 = ()
data T_Ordering_438
  = C_less_444 Integer | C_equal_448 | C_greater_454 Integer
-- Data.Nat.Base.compare
d_compare_460 :: Integer -> Integer -> T_Ordering_438
d_compare_460 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe C_equal_448
             _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe C_less_444 v2)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe C_greater_454 v2
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe (coe d_compare_460 (coe v2) (coe v3)))
-- Data.Nat.Base.s≤″s⁻¹
d_s'8804''8243's'8315''185'_514 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
d_s'8804''8243's'8315''185'_514 ~v0 ~v1 v2
  = du_s'8804''8243's'8315''185'_514 v2
du_s'8804''8243's'8315''185'_514 ::
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
du_s'8804''8243's'8315''185'_514 v0 = coe v0
