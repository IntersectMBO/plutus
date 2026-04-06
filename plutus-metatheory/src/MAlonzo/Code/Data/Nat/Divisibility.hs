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

module MAlonzo.Code.Data.Nat.Divisibility where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Double
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Nat.Divisibility.quotient≢0
d_quotient'8802'0_18 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_quotient'8802'0_18 ~v0 ~v1 ~v2 ~v3 = du_quotient'8802'0_18
du_quotient'8802'0_18 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_quotient'8802'0_18
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0'8658'm'8802'0_3968
-- Data.Nat.Divisibility.m∣n⇒n≡quotient*m
d_m'8739'n'8658'n'8801'quotient'42'm_28 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8739'n'8658'n'8801'quotient'42'm_28 = erased
-- Data.Nat.Divisibility.m∣n⇒n≡m*quotient
d_m'8739'n'8658'n'8801'm'42'quotient_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8739'n'8658'n'8801'm'42'quotient_34 = erased
-- Data.Nat.Divisibility.quotient-∣
d_quotient'45''8739'_46 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_quotient'45''8739'_46 v0 ~v1 ~v2 = du_quotient'45''8739'_46 v0
du_quotient'45''8739'_46 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_quotient'45''8739'_46 v0
  = coe MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v0
-- Data.Nat.Divisibility.quotient>1
d_quotient'62'1_54 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_quotient'62'1_54 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'42''45'cancel'737''45''60'_4354
      v0 (1 :: Integer)
      (MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
         (coe mulInt (coe v0) (coe (1 :: Integer)))
         (coe
            mulInt (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
            (\ v4 v5 v6 v7 v8 -> v8) (mulInt (coe v0) (coe (1 :: Integer))) v0
            (mulInt
               (coe v0)
               (coe
                  MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2)))
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
               v0 v1
               (mulInt
                  (coe v0)
                  (coe
                     MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                  (\ v4 v5 v6 v7 v8 -> v8) v1
                  (mulInt
                     (coe v0)
                     (coe
                        MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2)))
                  (mulInt
                     (coe v0)
                     (coe
                        MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                     (coe
                        mulInt (coe v0)
                        (coe
                           MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2))))
                  erased)
               v3)
            erased))
-- Data.Nat.Divisibility.quotient-<
d_quotient'45''60'_70 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_154 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_quotient'45''60'_70 v0 v1 v2 ~v3 ~v4
  = du_quotient'45''60'_70 v0 v1 v2
du_quotient'45''60'_70 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_quotient'45''60'_70 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
      (coe
         MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2))
      (coe v1)
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
         (MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2))
         (mulInt
            (coe
               MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2))
            (coe v0))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
            (\ v3 v4 v5 v6 v7 -> v7)
            (mulInt
               (coe
                  MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2))
               (coe v0))
            v1 v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
               (coe v1))
            erased)
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'60'm'42'n_4312
            (coe
               MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2))
            (coe v0)
            (coe MAlonzo.Code.Data.Nat.Base.du_nonTrivial'8658'n'62'1_178)))
-- Data.Nat.Divisibility.n/m≡quotient
d_n'47'm'8801'quotient_88 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'47'm'8801'quotient_88 = erased
-- Data.Nat.Divisibility.m%n≡0⇒n∣m
d_m'37'n'8801'0'8658'n'8739'm_100 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'37'n'8801'0'8658'n'8739'm_100 v0 v1 ~v2 ~v3
  = du_m'37'n'8801'0'8658'n'8739'm_100 v0 v1
du_m'37'n'8801'0'8658'n'8739'm_100 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'37'n'8801'0'8658'n'8739'm_100 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
-- Data.Nat.Divisibility._.[m/n]*n
d_'91'm'47'n'93''42'n_112 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'91'm'47'n'93''42'n_112 v0 v1 ~v2 ~v3
  = du_'91'm'47'n'93''42'n_112 v0 v1
du_'91'm'47'n'93''42'n_112 :: Integer -> Integer -> Integer
du_'91'm'47'n'93''42'n_112 v0 v1
  = coe
      mulInt
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v0) (coe v1))
      (coe v1)
-- Data.Nat.Divisibility.n∣m⇒m%n≡0
d_n'8739'm'8658'm'37'n'8801'0_122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8739'm'8658'm'37'n'8801'0_122 = erased
-- Data.Nat.Divisibility.m%n≡0⇔n∣m
d_m'37'n'8801'0'8660'n'8739'm_134 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_m'37'n'8801'0'8660'n'8739'm_134 v0 v1 ~v2
  = du_m'37'n'8801'0'8660'n'8739'm_134 v0 v1
du_m'37'n'8801'0'8660'n'8739'm_134 ::
  Integer ->
  Integer -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_m'37'n'8801'0'8660'n'8739'm_134 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
      (\ v2 -> coe du_m'37'n'8801'0'8658'n'8739'm_100 (coe v0) (coe v1))
      erased
-- Data.Nat.Divisibility.∣⇒≤
d_'8739''8658''8804'_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739''8658''8804'_142 ~v0 v1 ~v2 v3
  = du_'8739''8658''8804'_142 v1 v3
du_'8739''8658''8804'_142 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8739''8658''8804'_142 v0 v1
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0))
-- Data.Nat.Divisibility.>⇒∤
d_'62''8658''8740'_154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''8658''8740'_154 = erased
-- Data.Nat.Divisibility.∣-reflexive
d_'8739''45'reflexive_162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739''45'reflexive_162 ~v0 ~v1 ~v2 = du_'8739''45'reflexive_162
du_'8739''45'reflexive_162 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739''45'reflexive_162
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 (1 :: Integer)
-- Data.Nat.Divisibility.∣-refl
d_'8739''45'refl_166 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739''45'refl_166 ~v0 = du_'8739''45'refl_166
du_'8739''45'refl_166 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739''45'refl_166 = coe du_'8739''45'reflexive_162
-- Data.Nat.Divisibility.∣-trans
d_'8739''45'trans_168 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739''45'trans_168 ~v0 ~v1 ~v2 v3 v4
  = du_'8739''45'trans_168 v3 v4
du_'8739''45'trans_168 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739''45'trans_168 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                    (mulInt (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.∣-antisym
d_'8739''45'antisym_174 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45'antisym_174 = erased
-- Data.Nat.Divisibility._∣?_
d__'8739''63'__192 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8739''63'__192 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe
                          MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                          (0 :: Integer)))
             _ -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
             (coe du_m'37'n'8801'0'8660'n'8739'm_134 (coe v1) (coe v0))
             (MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
                (coe MAlonzo.Code.Data.Nat.Base.du__'37'__330 (coe v1) (coe v0))
                (coe (0 :: Integer)))
-- Data.Nat.Divisibility.∣-isPreorder
d_'8739''45'isPreorder_200 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8739''45'isPreorder_200
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8739''45'reflexive_162)
      (\ v0 v1 v2 v3 v4 -> coe du_'8739''45'trans_168 v3 v4)
-- Data.Nat.Divisibility.∣-isPartialOrder
d_'8739''45'isPartialOrder_202 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8739''45'isPartialOrder_202
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe d_'8739''45'isPreorder_200) erased
-- Data.Nat.Divisibility.∣-preorder
d_'8739''45'preorder_204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'8739''45'preorder_204
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      d_'8739''45'isPreorder_200
-- Data.Nat.Divisibility.∣-poset
d_'8739''45'poset_206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8739''45'poset_206
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      d_'8739''45'isPartialOrder_202
-- Data.Nat.Divisibility.∣-Reasoning.Base._IsRelatedTo_
d__IsRelatedTo__212 a0 a1 = ()
-- Data.Nat.Divisibility.∣-Reasoning.Base._∎
d__'8718'_214 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d__'8718'_214
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
               (coe v1))))
-- Data.Nat.Divisibility.∣-Reasoning.Base.IsEquality
d_IsEquality_216 a0 a1 a2 = ()
-- Data.Nat.Divisibility.∣-Reasoning.Base.IsEquality?
d_IsEquality'63'_218 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_218 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_IsEquality'63'_138
      v2
-- Data.Nat.Divisibility.∣-Reasoning.Base.begin_
d_begin__220 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_begin__220
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
               (coe v1))))
-- Data.Nat.Divisibility.∣-Reasoning.Base.begin_
d_begin__222 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__222 = erased
-- Data.Nat.Divisibility.∣-Reasoning.Base.equalitySubRelation
d_equalitySubRelation_224 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_equalitySubRelation_224
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152
-- Data.Nat.Divisibility.∣-Reasoning.Base.extractEquality
d_extractEquality_228 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T_IsEquality_122 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractEquality_228 = erased
-- Data.Nat.Divisibility.∣-Reasoning.Base.start
d_start_234 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_start_234
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-∼
d_step'45''8764'_236 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8764'_236
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_302
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
               (coe v1))))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≈
d_step'45''8776'_238 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776'_238
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776'_374
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
               (coe v1))))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≈-⟨
d_step'45''8776''45''10216'_240 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''45''10216'_240
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
               (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                  (coe v1)))))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≈-⟩
d_step'45''8776''45''10217'_242 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''45''10217'_242
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
               (coe v1))))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≈˘
d_step'45''8776''728'_244 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''728'_244
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''728'_376
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
               (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                  (coe v1)))))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≡
d_step'45''8801'_246 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801'_246
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≡-∣
d_step'45''8801''45''8739'_248 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''8739'_248 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_248 v2
du_step'45''8801''45''8739'_248 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''45''8739'_248 v0 = coe v0
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≡-⟨
d_step'45''8801''45''10216'_250 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''10216'_250
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≡-⟩
d_step'45''8801''45''10217'_252 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''10217'_252
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≡˘
d_step'45''8801''728'_254 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''728'_254
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_454
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Divisibility.∣-Reasoning.Base.step-≲
d_step'45''8818'_256 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8818'_256
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8818'_306
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
               (coe v1))))
-- Data.Nat.Divisibility.∣-Reasoning.Base.stop
d_stop_258 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_stop_258
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
-- Data.Nat.Divisibility.∣-Reasoning.Base.≈-go
d_'8776''45'go_260 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8776''45'go_260
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
-- Data.Nat.Divisibility.∣-Reasoning.Base.≡-go
d_'8801''45'go_262 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8801''45'go_262 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_262 v4
du_'8801''45'go_262 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_'8801''45'go_262 v0 = coe v0
-- Data.Nat.Divisibility.∣-Reasoning.Base.≲-go
d_'8818''45'go_264 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8818''45'go_264
  = let v0 = d_'8739''45'preorder_204 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
-- Data.Nat.Divisibility.∣-Reasoning._.step-∣
d_step'45''8739'_278 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8739'_278
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_334
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
         (coe d_'8739''45'isPreorder_200))
-- Data.Nat.Divisibility._∣0
d__'8739'0_282 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d__'8739'0_282 ~v0 = du__'8739'0_282
du__'8739'0_282 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du__'8739'0_282
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 (0 :: Integer)
-- Data.Nat.Divisibility.0∣⇒≡0
d_0'8739''8658''8801'0_286 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8739''8658''8801'0_286 = erased
-- Data.Nat.Divisibility.1∣_
d_1'8739'__294 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_1'8739'__294 v0
  = coe MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v0
-- Data.Nat.Divisibility.∣1⇒≡1
d_'8739'1'8658''8801'1_298 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'1'8658''8801'1_298 = erased
-- Data.Nat.Divisibility.n∣n
d_n'8739'n_304 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_n'8739'n_304 ~v0 = du_n'8739'n_304
du_n'8739'n_304 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_n'8739'n_304 = coe du_'8739''45'refl_166
-- Data.Nat.Divisibility.∣m∣n⇒∣m+n
d_'8739'm'8739'n'8658''8739'm'43'n_306 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739'm'8739'n'8658''8739'm'43'n_306 ~v0 ~v1 ~v2 v3 v4
  = du_'8739'm'8739'n'8658''8739'm'43'n_306 v3 v4
du_'8739'm'8739'n'8658''8739'm'43'n_306 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739'm'8739'n'8658''8739'm'43'n_306 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                    (addInt (coe v2) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.∣m+n∣m⇒∣n
d_'8739'm'43'n'8739'm'8658''8739'n_312 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739'm'43'n'8739'm'8658''8739'n_312 ~v0 ~v1 ~v2 v3 v4
  = du_'8739'm'43'n'8739'm'8658''8739'n_312 v3 v4
du_'8739'm'43'n'8739'm'8658''8739'n_312 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739'm'43'n'8739'm'8658''8739'n_312 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                    (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.n∣m*n
d_n'8739'm'42'n_338 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_n'8739'm'42'n_338 v0 ~v1 = du_n'8739'm'42'n_338 v0
du_n'8739'm'42'n_338 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_n'8739'm'42'n_338 v0
  = coe MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v0
-- Data.Nat.Divisibility.m∣m*n
d_m'8739'm'42'n_346 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'8739'm'42'n_346 ~v0 v1 = du_m'8739'm'42'n_346 v1
du_m'8739'm'42'n_346 ::
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'8739'm'42'n_346 v0
  = coe MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v0
-- Data.Nat.Divisibility.n∣m*n*o
d_n'8739'm'42'n'42'o_356 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_n'8739'm'42'n'42'o_356 v0 ~v1 v2
  = du_n'8739'm'42'n'42'o_356 v0 v2
du_n'8739'm'42'n'42'o_356 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_n'8739'm'42'n'42'o_356 v0 v1
  = coe
      du_'8739''45'trans_168 (coe du_n'8739'm'42'n_338 (coe v0))
      (coe du_m'8739'm'42'n_346 (coe v1))
-- Data.Nat.Divisibility.∣m⇒∣m*n
d_'8739'm'8658''8739'm'42'n_364 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739'm'8658''8739'm'42'n_364 ~v0 ~v1 v2 v3
  = du_'8739'm'8658''8739'm'42'n_364 v2 v3
du_'8739'm'8658''8739'm'42'n_364 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739'm'8658''8739'm'42'n_364 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v2
        -> coe
             du_'8739''45'trans_168 (coe du_n'8739'm'42'n_338 (coe v2))
             (coe du_m'8739'm'42'n_346 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.∣n⇒∣m*n
d_'8739'n'8658''8739'm'42'n_374 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739'n'8658''8739'm'42'n_374 ~v0 v1 ~v2
  = du_'8739'n'8658''8739'm'42'n_374 v1
du_'8739'n'8658''8739'm'42'n_374 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739'n'8658''8739'm'42'n_374 v0
  = coe du_'8739'm'8658''8739'm'42'n_364 (coe v0)
-- Data.Nat.Divisibility.m*n∣⇒m∣
d_m'42'n'8739''8658'm'8739'_388 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'42'n'8739''8658'm'8739'_388 ~v0 ~v1 v2 v3
  = du_m'42'n'8739''8658'm'8739'_388 v2 v3
du_m'42'n'8739''8658'm'8739'_388 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'42'n'8739''8658'm'8739'_388 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v2
        -> coe
             du_'8739'n'8658''8739'm'42'n_374 v2
             (coe du_m'8739'm'42'n_346 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.m*n∣⇒n∣
d_m'42'n'8739''8658'n'8739'_400 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'42'n'8739''8658'n'8739'_400 ~v0 v1 ~v2
  = du_m'42'n'8739''8658'n'8739'_400 v1
du_m'42'n'8739''8658'n'8739'_400 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'42'n'8739''8658'n'8739'_400 v0
  = coe du_m'42'n'8739''8658'm'8739'_388 (coe v0)
-- Data.Nat.Divisibility.*-pres-∣
d_'42''45'pres'45''8739'_410 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'pres'45''8739'_410 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'42''45'pres'45''8739'_410 v4 v5
du_'42''45'pres'45''8739'_410 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'42''45'pres'45''8739'_410 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                    (mulInt (coe v2) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.*-monoʳ-∣
d_'42''45'mono'691''45''8739'_426 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'mono'691''45''8739'_426 ~v0 ~v1 ~v2
  = du_'42''45'mono'691''45''8739'_426
du_'42''45'mono'691''45''8739'_426 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'42''45'mono'691''45''8739'_426
  = coe du_'42''45'pres'45''8739'_410 (coe du_'8739''45'refl_166)
-- Data.Nat.Divisibility.*-monoˡ-∣
d_'42''45'mono'737''45''8739'_432 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'mono'737''45''8739'_432 ~v0 ~v1 ~v2 v3
  = du_'42''45'mono'737''45''8739'_432 v3
du_'42''45'mono'737''45''8739'_432 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'42''45'mono'737''45''8739'_432 v0
  = coe
      du_'42''45'pres'45''8739'_410 (coe v0) (coe du_'8739''45'refl_166)
-- Data.Nat.Divisibility.*-cancelˡ-∣
d_'42''45'cancel'737''45''8739'_440 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'cancel'737''45''8739'_440 ~v0 ~v1 ~v2 ~v3 v4
  = du_'42''45'cancel'737''45''8739'_440 v4
du_'42''45'cancel'737''45''8739'_440 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'42''45'cancel'737''45''8739'_440 v0
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
      (coe du_q_454 (coe v0))
-- Data.Nat.Divisibility._.q
d_q_454 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 -> Integer
d_q_454 ~v0 ~v1 ~v2 ~v3 v4 = du_q_454 v4
du_q_454 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 -> Integer
du_q_454 v0
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v0)
-- Data.Nat.Divisibility.*-cancelʳ-∣
d_'42''45'cancel'691''45''8739'_462 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'cancel'691''45''8739'_462 ~v0 ~v1 ~v2 ~v3
  = du_'42''45'cancel'691''45''8739'_462
du_'42''45'cancel'691''45''8739'_462 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'42''45'cancel'691''45''8739'_462
  = coe du_'42''45'cancel'737''45''8739'_440
-- Data.Nat.Divisibility.∣m∸n∣n⇒∣m
d_'8739'm'8760'n'8739'n'8658''8739'm_480 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739'm'8760'n'8739'n'8658''8739'm_480 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8739'm'8760'n'8739'n'8658''8739'm_480 v4 v5
du_'8739'm'8760'n'8739'n'8658''8739'm_480 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739'm'8760'n'8739'n'8658''8739'm_480 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                    (addInt (coe v2) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.m/n∣m
d_m'47'n'8739'm_504 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'47'n'8739'm_504 v0 v1 ~v2 v3 = du_m'47'n'8739'm_504 v0 v1 v3
du_m'47'n'8739'm_504 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'47'n'8739'm_504 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
         (coe d_'8739''45'isPreorder_200))
      (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1) (coe v0)) v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
         (\ v3 v4 v5 v6 v7 -> v7)
         (coe MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1) (coe v0))
         (MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2)) v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_334
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
               (coe d_'8739''45'isPreorder_200))
            (MAlonzo.Code.Data.Nat.Divisibility.Core.d_quotient_30 (coe v2)) v1
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                  (coe d_'8739''45'isPreorder_200))
               (coe v1))
            (coe du_quotient'45''8739'_46 (coe v0)))
         erased)
-- Data.Nat.Divisibility.m*n∣o⇒m∣o/n
d_m'42'n'8739'o'8658'm'8739'o'47'n_522 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'42'n'8739'o'8658'm'8739'o'47'n_522 ~v0 ~v1 ~v2 ~v3 v4
  = du_m'42'n'8739'o'8658'm'8739'o'47'n_522 v4
du_m'42'n'8739'o'8658'm'8739'o'47'n_522 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'42'n'8739'o'8658'm'8739'o'47'n_522 v0 = coe v0
-- Data.Nat.Divisibility.m*n∣o⇒n∣o/m
d_m'42'n'8739'o'8658'n'8739'o'47'm_542 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'42'n'8739'o'8658'n'8739'o'47'm_542 ~v0 ~v1 ~v2 ~v3 v4
  = du_m'42'n'8739'o'8658'n'8739'o'47'm_542 v4
du_m'42'n'8739'o'8658'n'8739'o'47'm_542 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'42'n'8739'o'8658'n'8739'o'47'm_542 v0 = coe v0
-- Data.Nat.Divisibility.m∣n/o⇒m*o∣n
d_m'8739'n'47'o'8658'm'42'o'8739'n_554 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'8739'n'47'o'8658'm'42'o'8739'n_554 v0 ~v1 v2 ~v3 v4 v5
  = du_m'8739'n'47'o'8658'm'42'o'8739'n_554 v0 v2 v4 v5
du_m'8739'n'47'o'8658'm'42'o'8739'n_554 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'8739'n'47'o'8658'm'42'o'8739'n_554 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
                (coe d_'8739''45'isPreorder_200))
             (mulInt (coe v1) (coe v0)) (mulInt (coe v4) (coe v0))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_334
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                   (coe d_'8739''45'isPreorder_200))
                (mulInt (coe v1) (coe v0)) (mulInt (coe v4) (coe v0))
                (mulInt (coe v4) (coe v0))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                      (coe d_'8739''45'isPreorder_200))
                   (coe mulInt (coe v4) (coe v0)))
                (coe du_'42''45'mono'737''45''8739'_432 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.m∣n/o⇒o*m∣n
d_m'8739'n'47'o'8658'o'42'm'8739'n_574 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'8739'n'47'o'8658'o'42'm'8739'n_574 v0 ~v1 v2 ~v3
  = du_m'8739'n'47'o'8658'o'42'm'8739'n_574 v0 v2
du_m'8739'n'47'o'8658'o'42'm'8739'n_574 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'8739'n'47'o'8658'o'42'm'8739'n_574 v0 v1
  = coe du_m'8739'n'47'o'8658'm'42'o'8739'n_554 (coe v0) (coe v1)
-- Data.Nat.Divisibility.m/n∣o⇒m∣o*n
d_m'47'n'8739'o'8658'm'8739'o'42'n_586 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'47'n'8739'o'8658'm'8739'o'42'n_586 v0 ~v1 v2 ~v3 v4 v5
  = du_m'47'n'8739'o'8658'm'8739'o'42'n_586 v0 v2 v4 v5
du_m'47'n'8739'o'8658'm'8739'o'42'n_586 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'47'n'8739'o'8658'm'8739'o'42'n_586 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
                (coe d_'8739''45'isPreorder_200))
             (mulInt (coe v4) (coe v0)) (mulInt (coe v1) (coe v0))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_334
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                   (coe d_'8739''45'isPreorder_200))
                (mulInt (coe v4) (coe v0)) (mulInt (coe v1) (coe v0))
                (mulInt (coe v1) (coe v0))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                      (coe d_'8739''45'isPreorder_200))
                   (coe mulInt (coe v1) (coe v0)))
                (coe du_'42''45'mono'737''45''8739'_432 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.m∣n*o⇒m/n∣o
d_m'8739'n'42'o'8658'm'47'n'8739'o_606 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'8739'n'42'o'8658'm'47'n'8739'o_606 v0 ~v1 v2 ~v3 v4 v5
  = du_m'8739'n'42'o'8658'm'47'n'8739'o_606 v0 v2 v4 v5
du_m'8739'n'42'o'8658'm'47'n'8739'o_606 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'8739'n'42'o'8658'm'47'n'8739'o_606 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
                (coe d_'8739''45'isPreorder_200))
             (coe
                MAlonzo.Code.Data.Nat.Base.du__'47'__318
                (coe mulInt (coe v4) (coe v0)) (coe v0))
             v1
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                (\ v6 v7 v8 v9 v10 -> v10)
                (coe
                   MAlonzo.Code.Data.Nat.Base.du__'47'__318
                   (coe mulInt (coe v4) (coe v0)) (coe v0))
                v4 v1
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_334
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                      (coe d_'8739''45'isPreorder_200))
                   v4 v1 v1
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                         (coe d_'8739''45'isPreorder_200))
                      (coe v1))
                   (coe du_'42''45'cancel'691''45''8739'_462 v3))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.∣n∣m%n⇒∣m
d_'8739'n'8739'm'37'n'8658''8739'm_624 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8739'n'8739'm'37'n'8658''8739'm_624 ~v0 v1 v2 ~v3 v4 v5
  = du_'8739'n'8739'm'37'n'8658''8739'm_624 v1 v2 v4 v5
du_'8739'n'8739'm'37'n'8658''8739'm_624 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8739'n'8739'm'37'n'8658''8739'm_624 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                    (addInt
                       (coe
                          mulInt
                          (coe
                             MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v1)
                             (coe mulInt (coe v4) (coe v0)))
                          (coe v4))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.%-presˡ-∣
d_'37''45'pres'737''45''8739'_648 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'37''45'pres'737''45''8739'_648 v0 v1 ~v2 ~v3 v4 v5
  = du_'37''45'pres'737''45''8739'_648 v0 v1 v4 v5
du_'37''45'pres'737''45''8739'_648 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'37''45'pres'737''45''8739'_648 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v4
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.Core.C_divides_34
                    (coe
                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v4
                       (mulInt
                          (coe
                             MAlonzo.Code.Data.Nat.Base.du__'47'__318
                             (coe mulInt (coe v4) (coe v1)) (coe v0))
                          (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.m≤n⇒m!∣n!
d_m'8804'n'8658'm'33''8739'n'33'_670 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_m'8804'n'8658'm'33''8739'n'33'_670 ~v0 v1 v2
  = du_m'8804'n'8658'm'33''8739'n'33'_670 v1 v2
du_m'8804'n'8658'm'33''8739'n'33'_670 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_m'8804'n'8658'm'33''8739'n'33'_670 v0 v1
  = coe
      du_help_678 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''8242'_6238
         (coe v0) (coe v1))
-- Data.Nat.Divisibility._.help
d_help_678 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_help_678 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_help_678 v4 v5
du_help_678 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_help_678 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'reflexive_348
        -> coe du_'8739''45'refl_166
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_352 v3
        -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'8739'n'8658''8739'm'42'n_374 v0
                (coe du_help_678 (coe v4) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.hasNonTrivialDivisor-≢
d_hasNonTrivialDivisor'45''8802'_684 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_154 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_hasNonTrivialDivisor'45''8802'_684 v0 v1 ~v2 ~v3 ~v4 v5
  = du_hasNonTrivialDivisor'45''8802'_684 v0 v1 v5
du_hasNonTrivialDivisor'45''8802'_684 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
du_hasNonTrivialDivisor'45''8802'_684 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72
      v0
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_3060
         (coe v1) (coe du_'8739''8658''8804'_142 (coe v0) (coe v2)))
      v2
-- Data.Nat.Divisibility.hasNonTrivialDivisor-∣
d_hasNonTrivialDivisor'45''8739'_690 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_hasNonTrivialDivisor'45''8739'_690 ~v0 ~v1 ~v2 v3 v4
  = du_hasNonTrivialDivisor'45''8739'_690 v3 v4
du_hasNonTrivialDivisor'45''8739'_690 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
du_hasNonTrivialDivisor'45''8739'_690 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72 v2 v4 v5
        -> coe
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72
             v2 v4 (coe du_'8739''45'trans_168 (coe v5) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Divisibility.hasNonTrivialDivisor-≤
d_hasNonTrivialDivisor'45''8804'_698 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
d_hasNonTrivialDivisor'45''8804'_698 ~v0 ~v1 ~v2 v3 v4
  = du_hasNonTrivialDivisor'45''8804'_698 v3 v4
du_hasNonTrivialDivisor'45''8804'_698 ::
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__HasNonTrivialDivisorLessThan__50
du_hasNonTrivialDivisor'45''8804'_698 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72 v2 v4 v5
        -> coe
             MAlonzo.Code.Data.Nat.Divisibility.Core.C_hasNonTrivialDivisor_72
             v2
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
                (coe v4) (coe v1))
             v5
      _ -> MAlonzo.RTE.mazUnreachableError
