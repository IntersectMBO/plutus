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

module MAlonzo.Code.Data.Nat.Primality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.GCD
import qualified MAlonzo.Code.Data.Nat.ListAction.Properties
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Induction.Lexicographic
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Double
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Nat.Primality.recompute-nonTrivial
d_recompute'45'nonTrivial_16 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
d_recompute'45'nonTrivial_16 v0 ~v1
  = du_recompute'45'nonTrivial_16 v0
du_recompute'45'nonTrivial_16 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
du_recompute'45'nonTrivial_16 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_recompute_54
      (MAlonzo.Code.Data.Nat.Properties.d_nonTrivial'63'_2678 (coe v0))
      erased
-- Data.Nat.Primality._Rough_
d__Rough__22 :: Integer -> Integer -> ()
d__Rough__22 = erased
-- Data.Nat.Primality.Composite
d_Composite_28 :: Integer -> ()
d_Composite_28 = erased
-- Data.Nat.Primality.Prime
d_Prime_42 a0 = ()
data T_Prime_42 = C_prime_54
-- Data.Nat.Primality.Prime.notComposite
d_notComposite_52 ::
  T_Prime_42 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_notComposite_52 = erased
-- Data.Nat.Primality.Irreducible
d_Irreducible_56 :: Integer -> ()
d_Irreducible_56 = erased
-- Data.Nat.Primality.rough-1
d_rough'45'1_64 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rough'45'1_64 = erased
-- Data.Nat.Primality.0-rough
d_0'45'rough_68 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_0'45'rough_68 = erased
-- Data.Nat.Primality.1-rough
d_1'45'rough_70 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'45'rough_70 = erased
-- Data.Nat.Primality.2-rough
d_2'45'rough_72 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_2'45'rough_72 = erased
-- Data.Nat.Primality.rough⇒≤
d_rough'8658''8804'_74 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_rough'8658''8804'_74 v0 v1 ~v2 ~v3
  = du_rough'8658''8804'_74 v0 v1
du_rough'8658''8804'_74 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_rough'8658''8804'_74 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2958
      (coe v0) (coe v1)
-- Data.Nat.Primality._.n≮m
d_n'8814'm_82 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8814'm_82 = erased
-- Data.Nat.Primality.∤⇒rough-suc
d_'8740''8658'rough'45'suc_86 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8740''8658'rough'45'suc_86 = erased
-- Data.Nat.Primality.rough∧∣⇒rough
d_rough'8743''8739''8658'rough_120 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rough'8743''8739''8658'rough_120 = erased
-- Data.Nat.Primality.composite-≢
d_composite'45''8802'_130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_composite'45''8802'_130 v0 v1 ~v2 ~v3
  = du_composite'45''8802'_130 v0 v1
du_composite'45''8802'_130 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
du_composite'45''8802'_130 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.du_hasNonTrivialDivisor'45''8802'_684
      (coe v1) (coe v0) v3
-- Data.Nat.Primality.composite-∣
d_composite'45''8739'_134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_composite'45''8739'_134 ~v0 v1 ~v2 v3 v4
  = du_composite'45''8739'_134 v1 v3 v4
du_composite'45''8739'_134 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
du_composite'45''8739'_134 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72 v3 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72
                    (mulInt (coe v7) (coe v3))
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'691''45''60'_4168
                       (coe v7) (coe v0) (coe v5))
                    (coe
                       MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'mono'691''45''8739'_426
                       v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Primality._._
d___152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d___152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du___152
du___152 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du___152 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0'8658'm'8802'0_3882
-- Data.Nat.Primality.¬composite[0]
d_'172'composite'91'0'93'_154 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'composite'91'0'93'_154 = erased
-- Data.Nat.Primality.¬composite[1]
d_'172'composite'91'1'93'_156 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'composite'91'1'93'_156 = erased
-- Data.Nat.Primality.composite[4]
d_composite'91'4'93'_158 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_composite'91'4'93'_158
  = coe
      du_composite'45''8802'_130
      (mulInt (coe (2 :: Integer)) (coe (2 :: Integer))) (2 :: Integer)
      erased
      (coe
         MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
         (2 :: Integer))
-- Data.Nat.Primality.composite[6]
d_composite'91'6'93'_160 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_composite'91'6'93'_160
  = coe
      du_composite'45''8802'_130
      (mulInt (coe (2 :: Integer)) (coe (3 :: Integer))) (3 :: Integer)
      erased
      (coe
         MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
         (2 :: Integer))
-- Data.Nat.Primality.composite⇒nonZero
d_composite'8658'nonZero_162 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_composite'8658'nonZero_162 ~v0 ~v1
  = du_composite'8658'nonZero_162
du_composite'8658'nonZero_162 ::
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_composite'8658'nonZero_162
  = coe
      MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Primality.composite⇒nonTrivial
d_composite'8658'nonTrivial_164 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
d_composite'8658'nonTrivial_164 v0 ~v1
  = du_composite'8658'nonTrivial_164 v0
du_composite'8658'nonTrivial_164 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
du_composite'8658'nonTrivial_164 v0
  = case coe v0 of
      1 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> coe
             MAlonzo.Code.Data.Nat.Base.C_NonTrivial'46'constructor_5661
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Primality.composite?
d_composite'63'_168 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_composite'63'_168 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
      (coe du_CompositeUpTo'8660'Composite_202)
      (coe du_compositeUpTo'63'_204 (coe v0))
-- Data.Nat.Primality._.CompositeUpTo
d_CompositeUpTo_176 :: Integer -> Integer -> ()
d_CompositeUpTo_176 = erased
-- Data.Nat.Primality._.comp-upto⇒comp
d_comp'45'upto'8658'comp_182 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_comp'45'upto'8658'comp_182 ~v0 v1
  = du_comp'45'upto'8658'comp_182 v1
du_comp'45'upto'8658'comp_182 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
du_comp'45'upto'8658'comp_182 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72
                           v1 v3 v6
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Primality._.comp⇒comp-upto
d_comp'8658'comp'45'upto_196 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_comp'8658'comp'45'upto_196 ~v0 v1
  = du_comp'8658'comp'45'upto_196 v1
du_comp'8658'comp'45'upto_196 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_comp'8658'comp'45'upto_196 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72 v1 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe du_recompute'45'nonTrivial_16 (coe v1)) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Primality._.CompositeUpTo⇔Composite
d_CompositeUpTo'8660'Composite_202 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_CompositeUpTo'8660'Composite_202 ~v0
  = du_CompositeUpTo'8660'Composite_202
du_CompositeUpTo'8660'Composite_202 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_CompositeUpTo'8660'Composite_202
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2414
      (coe du_comp'45'upto'8658'comp_182)
      (coe du_comp'8658'comp'45'upto_196)
-- Data.Nat.Primality._.compositeUpTo?
d_compositeUpTo'63'_204 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_compositeUpTo'63'_204 ~v0 v1 = du_compositeUpTo'63'_204 v1
du_compositeUpTo'63'_204 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_compositeUpTo'63'_204 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_anyUpTo'63'_6446
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d_nonTrivial'63'_2678 (coe v1))
              (coe
                 MAlonzo.Code.Data.Nat.Divisibility.d__'8739''63'__192 (coe v1)
                 (coe v0))))
      (coe v0)
-- Data.Nat.Primality.¬prime[0]
d_'172'prime'91'0'93'_210 ::
  T_Prime_42 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'prime'91'0'93'_210 = erased
-- Data.Nat.Primality.¬prime[1]
d_'172'prime'91'1'93'_212 ::
  T_Prime_42 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'prime'91'1'93'_212 = erased
-- Data.Nat.Primality.prime[2]
d_prime'91'2'93'_214 :: T_Prime_42
d_prime'91'2'93'_214 = erased
-- Data.Nat.Primality.prime⇒nonZero
d_prime'8658'nonZero_216 ::
  Integer -> T_Prime_42 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_prime'8658'nonZero_216 ~v0 ~v1 = du_prime'8658'nonZero_216
du_prime'8658'nonZero_216 ::
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_prime'8658'nonZero_216
  = coe MAlonzo.Code.Data.Nat.Base.du_nonTrivial'8658'nonZero_170
-- Data.Nat.Primality.prime⇒nonTrivial
d_prime'8658'nonTrivial_218 ::
  Integer ->
  T_Prime_42 -> MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
d_prime'8658'nonTrivial_218 v0 ~v1
  = du_prime'8658'nonTrivial_218 v0
du_prime'8658'nonTrivial_218 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
du_prime'8658'nonTrivial_218 v0
  = coe du_recompute'45'nonTrivial_16 (coe v0)
-- Data.Nat.Primality.prime?
d_prime'63'_220 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_prime'63'_220 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      1 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
             (coe du_PrimeUpTo'8660'Prime_262)
             (coe du_primeUpTo'63'_264 (coe v0))
-- Data.Nat.Primality._.PrimeUpTo
d_PrimeUpTo_228 :: Integer -> Integer -> ()
d_PrimeUpTo_228 = erased
-- Data.Nat.Primality._.prime⇒prime-upto
d_prime'8658'prime'45'upto_234 ::
  Integer ->
  T_Prime_42 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_prime'8658'prime'45'upto_234 = erased
-- Data.Nat.Primality._.prime-upto⇒prime
d_prime'45'upto'8658'prime_252 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Prime_42
d_prime'45'upto'8658'prime_252 = erased
-- Data.Nat.Primality._.PrimeUpTo⇔Prime
d_PrimeUpTo'8660'Prime_262 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_PrimeUpTo'8660'Prime_262 ~v0 ~v1 = du_PrimeUpTo'8660'Prime_262
du_PrimeUpTo'8660'Prime_262 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_PrimeUpTo'8660'Prime_262
  = coe MAlonzo.Code.Function.Bundles.du_mk'8660'_2414 erased erased
-- Data.Nat.Primality._.primeUpTo?
d_primeUpTo'63'_264 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_primeUpTo'63'_264 ~v0 v1 = du_primeUpTo'63'_264 v1
du_primeUpTo'63'_264 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_primeUpTo'63'_264 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_allUpTo'63'_6510
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8594''45'dec__106
              (coe
                 MAlonzo.Code.Data.Nat.Properties.d_nonTrivial'63'_2678 (coe v1))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
                 (coe
                    MAlonzo.Code.Data.Nat.Divisibility.d__'8739''63'__192 (coe v1)
                    (coe v0)))))
      (coe v0)
-- Data.Nat.Primality.euclidsLemma
d_euclidsLemma_276 ::
  Integer ->
  Integer ->
  Integer ->
  T_Prime_42 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_euclidsLemma_276 v0 v1 v2 ~v3 v4
  = du_euclidsLemma_276 v0 v1 v2 v4
du_euclidsLemma_276 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_euclidsLemma_276 v0 v1 v2 v3
  = coe du_result_302 (coe v0) (coe v1) (coe v2) (coe v3)
-- Data.Nat.Primality._.p∣rmn
d_p'8739'rmn_298 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_p'8739'rmn_298 v0 v1 v2 ~v3 ~v4 v5 v6
  = du_p'8739'rmn_298 v0 v1 v2 v5 v6
du_p'8739'rmn_298 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_p'8739'rmn_298 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
            (coe v5))
         v2 (mulInt (coe mulInt (coe v4) (coe v0)) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
               (coe
                  MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
            v2 (mulInt (coe v0) (coe v1))
            (mulInt (coe mulInt (coe v4) (coe v0)) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe
                     MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
               (mulInt (coe v0) (coe v1))
               (mulInt (coe v4) (coe mulInt (coe v0) (coe v1)))
               (mulInt (coe mulInt (coe v4) (coe v0)) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                  (\ v6 v7 v8 v9 v10 -> v10)
                  (mulInt (coe v4) (coe mulInt (coe v0) (coe v1)))
                  (mulInt (coe mulInt (coe v4) (coe v0)) (coe v1))
                  (mulInt (coe mulInt (coe v4) (coe v0)) (coe v1))
                  (let v6
                         = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                           (coe v6))
                        (coe mulInt (coe mulInt (coe v4) (coe v0)) (coe v1))))
                  erased)
               (coe
                  MAlonzo.Code.Data.Nat.Divisibility.du_n'8739'm'42'n_338 (coe v4)))
            v3))
-- Data.Nat.Primality._.result
d_result_302 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_result_302 v0 v1 v2 ~v3 ~v4 v5 = du_result_302 v0 v1 v2 v5
du_result_302 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_result_302 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Data.Nat.GCD.du_gcd'8243'_1098
              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v2))
              (coe
                 MAlonzo.Code.Induction.Lexicographic.du_'91'_'8855'_'93'_166
                 (\ v4 v5 v6 v7 ->
                    coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v5 v7)
                 (\ v4 v5 v6 v7 ->
                    coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v5 v7)
                 erased (coe MAlonzo.Code.Data.Nat.GCD.du_gcd'8243'_1098)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v2))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Nat.GCD.C_result_1032 v5 v6 v7
           -> case coe v5 of
                0 -> coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased
                1 -> case coe v7 of
                       MAlonzo.Code.Data.Nat.GCD.C_'43''45'_858 v8 v9
                         -> coe
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                              (coe
                                 MAlonzo.Code.Data.Nat.Divisibility.du_'8739'm'43'n'8739'm'8658''8739'n_312
                                 (let v11
                                        = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                                  coe
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
                                          (coe v11))
                                       v2
                                       (addInt
                                          (coe mulInt (coe mulInt (coe v9) (coe v2)) (coe v1))
                                          (coe v1))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                                             (coe
                                                MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
                                          v2 (mulInt (coe mulInt (coe v8) (coe v0)) (coe v1))
                                          (addInt
                                             (coe mulInt (coe mulInt (coe v9) (coe v2)) (coe v1))
                                             (coe v1))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                             (\ v12 v13 v14 v15 v16 -> v16)
                                             (mulInt (coe mulInt (coe v8) (coe v0)) (coe v1))
                                             (addInt
                                                (coe mulInt (coe mulInt (coe v9) (coe v2)) (coe v1))
                                                (coe v1))
                                             (addInt
                                                (coe mulInt (coe mulInt (coe v9) (coe v2)) (coe v1))
                                                (coe v1))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                (\ v12 v13 v14 v15 v16 -> v16)
                                                (addInt
                                                   (coe
                                                      mulInt (coe mulInt (coe v9) (coe v2))
                                                      (coe v1))
                                                   (coe v1))
                                                (addInt
                                                   (coe
                                                      mulInt (coe mulInt (coe v9) (coe v2))
                                                      (coe v1))
                                                   (coe v1))
                                                (addInt
                                                   (coe
                                                      mulInt (coe mulInt (coe v9) (coe v2))
                                                      (coe v1))
                                                   (coe v1))
                                                (let v12
                                                       = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                      (coe
                                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                                         (coe v12))
                                                      (coe
                                                         addInt
                                                         (coe
                                                            mulInt (coe mulInt (coe v9) (coe v2))
                                                            (coe v1))
                                                         (coe v1))))
                                                erased)
                                             erased)
                                          (coe
                                             du_p'8739'rmn_298 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v8)))))
                                 (coe
                                    MAlonzo.Code.Data.Nat.Divisibility.du_n'8739'm'42'n'42'o_356
                                    (coe v9) (coe v1)))
                       MAlonzo.Code.Data.Nat.GCD.C_'45''43'_866 v8 v9
                         -> coe
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                              (coe
                                 MAlonzo.Code.Data.Nat.Divisibility.du_'8739'm'43'n'8739'm'8658''8739'n_312
                                 (let v11
                                        = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                                  coe
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
                                          (coe v11))
                                       v2
                                       (addInt
                                          (coe mulInt (coe mulInt (coe v8) (coe v0)) (coe v1))
                                          (coe v1))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                                             (coe
                                                MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
                                          v2 (mulInt (coe mulInt (coe v9) (coe v2)) (coe v1))
                                          (addInt
                                             (coe mulInt (coe mulInt (coe v8) (coe v0)) (coe v1))
                                             (coe v1))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                             (\ v12 v13 v14 v15 v16 -> v16)
                                             (mulInt (coe mulInt (coe v9) (coe v2)) (coe v1))
                                             (addInt
                                                (coe mulInt (coe mulInt (coe v8) (coe v0)) (coe v1))
                                                (coe v1))
                                             (addInt
                                                (coe mulInt (coe mulInt (coe v8) (coe v0)) (coe v1))
                                                (coe v1))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                (\ v12 v13 v14 v15 v16 -> v16)
                                                (addInt
                                                   (coe
                                                      mulInt (coe mulInt (coe v8) (coe v0))
                                                      (coe v1))
                                                   (coe v1))
                                                (addInt
                                                   (coe
                                                      mulInt (coe mulInt (coe v8) (coe v0))
                                                      (coe v1))
                                                   (coe v1))
                                                (addInt
                                                   (coe
                                                      mulInt (coe mulInt (coe v8) (coe v0))
                                                      (coe v1))
                                                   (coe v1))
                                                (let v12
                                                       = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                      (coe
                                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                                         (coe v12))
                                                      (coe
                                                         addInt
                                                         (coe
                                                            mulInt (coe mulInt (coe v8) (coe v0))
                                                            (coe v1))
                                                         (coe v1))))
                                                erased)
                                             erased)
                                          (coe
                                             MAlonzo.Code.Data.Nat.Divisibility.du_n'8739'm'42'n'42'o_356
                                             (coe v9) (coe v1)))))
                                 (coe
                                    du_p'8739'rmn_298 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> let v8
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v8 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2700
                                    (coe v5))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                  (coe eqInt (coe v5) (coe v2))) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                            -> if coe v9
                                 then coe
                                        seq (coe v10)
                                        (coe
                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                           (coe
                                              MAlonzo.Code.Data.Nat.GCD.du_gcd'8739'm_642 (coe v6)))
                                 else coe
                                        seq (coe v10)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                           erased)
                          _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Primality.prime⇒rough
d_prime'8658'rough_346 ::
  Integer ->
  T_Prime_42 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_prime'8658'rough_346 = erased
-- Data.Nat.Primality.rough∧∣⇒prime
d_rough'8743''8739''8658'prime_350 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 -> T_Prime_42
d_rough'8743''8739''8658'prime_350 = erased
-- Data.Nat.Primality.rough∧square>⇒prime
d_rough'8743'square'62''8658'prime_356 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_Prime_42
d_rough'8743'square'62''8658'prime_356 = erased
-- Data.Nat.Primality._.¬composite
d_'172'composite_366 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'composite_366 = erased
-- Data.Nat.Primality.composite⇒¬prime
d_composite'8658''172'prime_378 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  T_Prime_42 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_composite'8658''172'prime_378 = erased
-- Data.Nat.Primality.¬composite⇒prime
d_'172'composite'8658'prime_384 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Prime_42
d_'172'composite'8658'prime_384 = erased
-- Data.Nat.Primality.prime⇒¬composite
d_prime'8658''172'composite_386 ::
  Integer ->
  T_Prime_42 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_prime'8658''172'composite_386 = erased
-- Data.Nat.Primality.¬prime⇒composite
d_'172'prime'8658'composite_390 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (T_Prime_42 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_'172'prime'8658'composite_390 v0 ~v1 ~v2
  = du_'172'prime'8658'composite_390 v0
du_'172'prime'8658'composite_390 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
du_'172'prime'8658'composite_390 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_decidable'45'stable_198
      (coe d_composite'63'_168 (coe v0))
-- Data.Nat.Primality.productOfPrimes≢0
d_productOfPrimes'8802'0_398 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_productOfPrimes'8802'0_398 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.ListAction.Properties.du_product'8802'0_148
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (\ v2 v3 -> coe du_prime'8658'nonZero_216) (coe v0) (coe v1))
-- Data.Nat.Primality.productOfPrimes≥1
d_productOfPrimes'8805'1_404 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_productOfPrimes'8805'1_404 ~v0 ~v1
  = du_productOfPrimes'8805'1_404
du_productOfPrimes'8805'1_404 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_productOfPrimes'8805'1_404
  = coe MAlonzo.Code.Data.Nat.Base.du_'62''45'nonZero'8315''185'_146
-- Data.Nat.Primality.¬irreducible[0]
d_'172'irreducible'91'0'93'_410 ::
  (Integer ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'irreducible'91'0'93'_410 = erased
-- Data.Nat.Primality._.2≡1⊎2≡0
d_2'8801'1'8846'2'8801'0_418 ::
  (Integer ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_2'8801'1'8846'2'8801'0_418 v0
  = coe
      v0 (2 :: Integer)
      (coe
         MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
         (0 :: Integer))
-- Data.Nat.Primality.irreducible[1]
d_irreducible'91'1'93'_420 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_irreducible'91'1'93'_420 ~v0 ~v1 = du_irreducible'91'1'93'_420
du_irreducible'91'1'93'_420 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_irreducible'91'1'93'_420
  = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
-- Data.Nat.Primality.irreducible[2]
d_irreducible'91'2'93'_424 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_irreducible'91'2'93'_424 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Nat.Divisibility.du_'8739''8658''8804'_142
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
           -> case coe v5 of
                MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                  -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                  -> coe
                       seq (coe v8) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Primality.irreducible⇒nonZero
d_irreducible'8658'nonZero_442 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_irreducible'8658'nonZero_442 v0
  = case coe v0 of
      0 -> coe
             (\ v1 ->
                coe
                  MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                  erased)
      _ -> coe
             (\ v1 ->
                coe
                  MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Nat.Primality.irreducible?
d_irreducible'63'_444 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_irreducible'63'_444 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
                (coe du_IrreducibleUpTo'8660'Irreducible_472 (coe v1))
                (coe du_irreducibleUpTo'63'_474 (coe v0)))
-- Data.Nat.Primality._.IrreducibleUpTo
d_IrreducibleUpTo_452 :: Integer -> Integer -> ()
d_IrreducibleUpTo_452 = erased
-- Data.Nat.Primality._.irr-upto⇒irr
d_irr'45'upto'8658'irr_458 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_irr'45'upto'8658'irr_458 v0 ~v1 v2 v3 v4
  = du_irr'45'upto'8658'irr_458 v0 v2 v3 v4
du_irr'45'upto'8658'irr_458 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_irr'45'upto'8658'irr_458 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v4 -> coe v1 v2 v4 v3)
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
      (MAlonzo.Code.Data.Nat.Properties.d_m'8804'n'8658'm'60'n'8744'm'8801'n_3174
         (coe v2) (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Data.Nat.Divisibility.du_'8739''8658''8804'_142
            (coe v2) (coe v3)))
-- Data.Nat.Primality._.irr⇒irr-upto
d_irr'8658'irr'45'upto_464 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_irr'8658'irr'45'upto_464 ~v0 v1 v2 ~v3 v4
  = du_irr'8658'irr'45'upto_464 v1 v2 v4
du_irr'8658'irr'45'upto_464 ::
  (Integer ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_irr'8658'irr'45'upto_464 v0 v1 v2 = coe v0 v1 v2
-- Data.Nat.Primality._.IrreducibleUpTo⇔Irreducible
d_IrreducibleUpTo'8660'Irreducible_472 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_IrreducibleUpTo'8660'Irreducible_472 v0 ~v1
  = du_IrreducibleUpTo'8660'Irreducible_472 v0
du_IrreducibleUpTo'8660'Irreducible_472 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_IrreducibleUpTo'8660'Irreducible_472 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2414
      (coe du_irr'45'upto'8658'irr_458 (coe v0))
      (\ v1 v2 v3 v4 -> coe du_irr'8658'irr'45'upto_464 v1 v2 v4)
-- Data.Nat.Primality._.irreducibleUpTo?
d_irreducibleUpTo'63'_474 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_irreducibleUpTo'63'_474 ~v0 v1 = du_irreducibleUpTo'63'_474 v1
du_irreducibleUpTo'63'_474 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_irreducibleUpTo'63'_474 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_allUpTo'63'_6510
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8594''45'dec__106
              (coe
                 MAlonzo.Code.Data.Nat.Divisibility.d__'8739''63'__192 (coe v1)
                 (coe v0))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                 (coe
                    MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710 (coe v1)
                    (coe (1 :: Integer)))
                 (coe
                    MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710 (coe v1)
                    (coe v0)))))
      (coe v0)
-- Data.Nat.Primality.prime⇒irreducible
d_prime'8658'irreducible_480 ::
  Integer ->
  T_Prime_42 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_prime'8658'irreducible_480 ~v0 ~v1 v2
  = du_prime'8658'irreducible_480 v2
du_prime'8658'irreducible_480 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_prime'8658'irreducible_480 v0 v1 = coe du_irr_494 (coe v0)
-- Data.Nat.Primality._.irr
d_irr_494 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_irr_494 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_irr_494 v5
du_irr_494 :: Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_irr_494 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      1 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Nat.Primality._._.d≮p
d_d'8814'p_506 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_d'8814'p_506 = erased
-- Data.Nat.Primality.irreducible⇒prime
d_irreducible'8658'prime_510 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  T_Prime_42
d_irreducible'8658'prime_510 = erased
