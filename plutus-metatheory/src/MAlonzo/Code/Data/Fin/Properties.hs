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

module MAlonzo.Code.Data.Fin.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Definitions.RawMagma
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Effect.Applicative
import qualified MAlonzo.Code.Effect.Functor
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Relation.Unary.Properties

-- Data.Fin.Properties.¬Fin0
d_'172'Fin0_20 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'Fin0_20 = erased
-- Data.Fin.Properties.nonZeroIndex
d_nonZeroIndex_22 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_nonZeroIndex_22 ~v0 ~v1 = du_nonZeroIndex_22
du_nonZeroIndex_22 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_nonZeroIndex_22
  = coe
      MAlonzo.Code.Data.Nat.Base.C_constructor_120
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Fin.Properties.0↔⊥
d_0'8596''8869'_24 :: MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_0'8596''8869'_24
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542 erased
      erased
-- Data.Fin.Properties.1↔⊤
d_1'8596''8868'_26 :: MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_1'8596''8868'_26
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         (\ v0 -> seq (coe v0) (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Data.Fin.Properties..extendedlambda3
d_'46'extendedlambda3_34 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda3_34 = erased
-- Data.Fin.Properties.2↔Bool
d_2'8596'Bool_36 :: MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_2'8596'Bool_36
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe d_'46'extendedlambda4_38)
      (coe
         (\ v0 ->
            if coe v0
              then coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
              else coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Data.Fin.Properties..extendedlambda4
d_'46'extendedlambda4_38 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Bool
d_'46'extendedlambda4_38 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v2
        -> coe seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties..extendedlambda7
d_'46'extendedlambda7_44 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda7_44 = erased
-- Data.Fin.Properties.0≢1+n
d_0'8802'1'43'n_46 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_0'8802'1'43'n_46 = erased
-- Data.Fin.Properties.suc-injective
d_suc'45'injective_48 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'injective_48 = erased
-- Data.Fin.Properties._≟_
d__'8799'__50 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__50 ~v0 v1 v2 = du__'8799'__50 v1 v2
du__'8799'__50 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__50 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased erased (coe du__'8799'__50 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.≡-isDecEquivalence
d_'8801''45'isDecEquivalence_60 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_'8801''45'isDecEquivalence_60 ~v0
  = du_'8801''45'isDecEquivalence_60
du_'8801''45'isDecEquivalence_60 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_'8801''45'isDecEquivalence_60
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe du__'8799'__50)
-- Data.Fin.Properties.≡-preorder
d_'8801''45'preorder_62 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'8801''45'preorder_62 ~v0 = du_'8801''45'preorder_62
du_'8801''45'preorder_62 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_'8801''45'preorder_62
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_preorder_414
-- Data.Fin.Properties.≡-setoid
d_'8801''45'setoid_66 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_66 ~v0 = du_'8801''45'setoid_66
du_'8801''45'setoid_66 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_'8801''45'setoid_66
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Fin.Properties.≡-decSetoid
d_'8801''45'decSetoid_70 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_70 ~v0 = du_'8801''45'decSetoid_70
du_'8801''45'decSetoid_70 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_'8801''45'decSetoid_70
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      (coe du_'8801''45'isDecEquivalence_60)
-- Data.Fin.Properties.toℕ-injective
d_toℕ'45'injective_74 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'injective_74 = erased
-- Data.Fin.Properties.toℕ-strengthen
d_toℕ'45'strengthen_90 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'strengthen_90 = erased
-- Data.Fin.Properties.toℕ-↑ˡ
d_toℕ'45''8593''737'_98 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45''8593''737'_98 = erased
-- Data.Fin.Properties.↑ˡ-injective
d_'8593''737''45'injective_112 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8593''737''45'injective_112 = erased
-- Data.Fin.Properties.toℕ-↑ʳ
d_toℕ'45''8593''691'_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45''8593''691'_128 = erased
-- Data.Fin.Properties.↑ʳ-injective
d_'8593''691''45'injective_142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8593''691''45'injective_142 = erased
-- Data.Fin.Properties.toℕ<n
d_toℕ'60'n_156 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'60'n_156 ~v0 v1 = du_toℕ'60'n_156 v1
du_toℕ'60'n_156 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'60'n_156 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_toℕ'60'n_156 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.toℕ≤pred[n]
d_toℕ'8804'pred'91'n'93'_162 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'8804'pred'91'n'93'_162 ~v0 v1
  = du_toℕ'8804'pred'91'n'93'_162 v1
du_toℕ'8804'pred'91'n'93'_162 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'8804'pred'91'n'93'_162 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_toℕ'8804'pred'91'n'93'_162 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.toℕ≤n
d_toℕ'8804'n_170 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'8804'n_170 ~v0 v1 = du_toℕ'8804'n_170 v1
du_toℕ'8804'n_170 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'8804'n_170 v0 = coe du_toℕ'8804'pred'91'n'93'_162 (coe v0)
-- Data.Fin.Properties.toℕ≤pred[n]′
d_toℕ'8804'pred'91'n'93''8242'_178 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'8804'pred'91'n'93''8242'_178 ~v0 v1
  = du_toℕ'8804'pred'91'n'93''8242'_178 v1
du_toℕ'8804'pred'91'n'93''8242'_178 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'8804'pred'91'n'93''8242'_178 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'pred_5806
      (coe du_toℕ'60'n_156 (coe v0))
-- Data.Fin.Properties.toℕ-mono-<
d_toℕ'45'mono'45''60'_182 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'mono'45''60'_182 ~v0 ~v1 ~v2 v3
  = du_toℕ'45'mono'45''60'_182 v3
du_toℕ'45'mono'45''60'_182 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'45'mono'45''60'_182 v0 = coe v0
-- Data.Fin.Properties.toℕ-mono-≤
d_toℕ'45'mono'45''8804'_186 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'mono'45''8804'_186 ~v0 ~v1 ~v2 v3
  = du_toℕ'45'mono'45''8804'_186 v3
du_toℕ'45'mono'45''8804'_186 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'45'mono'45''8804'_186 v0 = coe v0
-- Data.Fin.Properties.toℕ-cancel-≤
d_toℕ'45'cancel'45''8804'_190 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'cancel'45''8804'_190 ~v0 ~v1 ~v2 v3
  = du_toℕ'45'cancel'45''8804'_190 v3
du_toℕ'45'cancel'45''8804'_190 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'45'cancel'45''8804'_190 v0 = coe v0
-- Data.Fin.Properties.toℕ-cancel-<
d_toℕ'45'cancel'45''60'_194 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'cancel'45''60'_194 ~v0 ~v1 ~v2 v3
  = du_toℕ'45'cancel'45''60'_194 v3
du_toℕ'45'cancel'45''60'_194 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'45'cancel'45''60'_194 v0 = coe v0
-- Data.Fin.Properties.toℕ-fromℕ
d_toℕ'45'fromℕ_200 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'fromℕ_200 = erased
-- Data.Fin.Properties.fromℕ-toℕ
d_fromℕ'45'toℕ_206 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'45'toℕ_206 = erased
-- Data.Fin.Properties.≤fromℕ
d_'8804'fromℕ_212 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804'fromℕ_212 ~v0 v1 = du_'8804'fromℕ_212 v1
du_'8804'fromℕ_212 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804'fromℕ_212 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62
      (coe du_toℕ'60'n_156 (coe v0))
-- Data.Fin.Properties.fromℕ<-toℕ
d_fromℕ'60''45'toℕ_226 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'60''45'toℕ_226 = erased
-- Data.Fin.Properties.toℕ-fromℕ<
d_toℕ'45'fromℕ'60'_234 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'fromℕ'60'_234 = erased
-- Data.Fin.Properties.fromℕ-def
d_fromℕ'45'def_242 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'45'def_242 = erased
-- Data.Fin.Properties.fromℕ<-cong
d_fromℕ'60''45'cong_256 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'60''45'cong_256 = erased
-- Data.Fin.Properties.fromℕ<-injective
d_fromℕ'60''45'injective_274 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'60''45'injective_274 = erased
-- Data.Fin.Properties.fromℕ<≡fromℕ<″
d_fromℕ'60''8801'fromℕ'60''8243'_286 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'60''8801'fromℕ'60''8243'_286 = erased
-- Data.Fin.Properties.toℕ-fromℕ<″
d_toℕ'45'fromℕ'60''8243'_296 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'fromℕ'60''8243'_296 = erased
-- Data.Fin.Properties.toℕ-cast
d_toℕ'45'cast_312 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'cast_312 = erased
-- Data.Fin.Properties.cast-is-id
d_cast'45'is'45'id_328 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cast'45'is'45'id_328 = erased
-- Data.Fin.Properties.subst-is-cast
d_subst'45'is'45'cast_340 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'is'45'cast_340 = erased
-- Data.Fin.Properties.cast-trans
d_cast'45'trans_350 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cast'45'trans_350 = erased
-- Data.Fin.Properties.cast-involutive
d_cast'45'involutive_368 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cast'45'involutive_368 = erased
-- Data.Fin.Properties.≤-reflexive
d_'8804''45'reflexive_376 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'reflexive_376 ~v0 v1 ~v2 ~v3
  = du_'8804''45'reflexive_376 v1
du_'8804''45'reflexive_376 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'reflexive_376 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
-- Data.Fin.Properties.≤-refl
d_'8804''45'refl_378 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'refl_378 ~v0 v1 = du_'8804''45'refl_378 v1
du_'8804''45'refl_378 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'refl_378 v0 = coe du_'8804''45'reflexive_376 (coe v0)
-- Data.Fin.Properties.≤-trans
d_'8804''45'trans_380 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'trans_380 ~v0 ~v1 ~v2 ~v3 = du_'8804''45'trans_380
du_'8804''45'trans_380 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'trans_380
  = coe MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
-- Data.Fin.Properties.≤-antisym
d_'8804''45'antisym_382 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_382 = erased
-- Data.Fin.Properties.≤-total
d_'8804''45'total_388 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_388 ~v0 v1 v2 = du_'8804''45'total_388 v1 v2
du_'8804''45'total_388 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''45'total_388 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'total_2928
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
-- Data.Fin.Properties.≤-irrelevant
d_'8804''45'irrelevant_394 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_394 = erased
-- Data.Fin.Properties._≤?_
d__'8804''63'__396 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__396 ~v0 ~v1 v2 v3 = du__'8804''63'__396 v2 v3
du__'8804''63'__396 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8804''63'__396 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2920
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
-- Data.Fin.Properties._<?_
d__'60''63'__402 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__402 ~v0 ~v1 v2 v3 = du__'60''63'__402 v2 v3
du__'60''63'__402 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__402 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2920
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0)))
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
-- Data.Fin.Properties.≤-isPreorder
d_'8804''45'isPreorder_408 ::
  Integer -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8804''45'isPreorder_408 ~v0 = du_'8804''45'isPreorder_408
du_'8804''45'isPreorder_408 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_'8804''45'isPreorder_408
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_376 v0)
      (\ v0 v1 v2 -> coe du_'8804''45'trans_380)
-- Data.Fin.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_410 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8804''45'isPartialOrder_410 ~v0
  = du_'8804''45'isPartialOrder_410
du_'8804''45'isPartialOrder_410 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'8804''45'isPartialOrder_410
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe du_'8804''45'isPreorder_408) erased
-- Data.Fin.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_412 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8804''45'isTotalOrder_412 ~v0 = du_'8804''45'isTotalOrder_412
du_'8804''45'isTotalOrder_412 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_'8804''45'isTotalOrder_412
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe du_'8804''45'isPartialOrder_410) (coe du_'8804''45'total_388)
-- Data.Fin.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_414 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8804''45'isDecTotalOrder_414 ~v0
  = du_'8804''45'isDecTotalOrder_414
du_'8804''45'isDecTotalOrder_414 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_'8804''45'isDecTotalOrder_414
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe du_'8804''45'isTotalOrder_412) (coe du__'8799'__50)
      (coe du__'8804''63'__396)
-- Data.Fin.Properties.≤-preorder
d_'8804''45'preorder_416 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'8804''45'preorder_416 ~v0 = du_'8804''45'preorder_416
du_'8804''45'preorder_416 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_'8804''45'preorder_416
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      (coe du_'8804''45'isPreorder_408)
-- Data.Fin.Properties.≤-poset
d_'8804''45'poset_420 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8804''45'poset_420 ~v0 = du_'8804''45'poset_420
du_'8804''45'poset_420 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_'8804''45'poset_420
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (coe du_'8804''45'isPartialOrder_410)
-- Data.Fin.Properties.≤-totalOrder
d_'8804''45'totalOrder_424 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_'8804''45'totalOrder_424 ~v0 = du_'8804''45'totalOrder_424
du_'8804''45'totalOrder_424 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
du_'8804''45'totalOrder_424
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1090
      (coe du_'8804''45'isTotalOrder_412)
-- Data.Fin.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_428 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_'8804''45'decTotalOrder_428 ~v0 = du_'8804''45'decTotalOrder_428
du_'8804''45'decTotalOrder_428 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
du_'8804''45'decTotalOrder_428
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      (coe du_'8804''45'isDecTotalOrder_414)
-- Data.Fin.Properties.<-irrefl
d_'60''45'irrefl_432 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_432 = erased
-- Data.Fin.Properties.<-asym
d_'60''45'asym_434 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_434 = erased
-- Data.Fin.Properties.<-trans
d_'60''45'trans_436 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans_436 ~v0 ~v1 v2 ~v3 = du_'60''45'trans_436 v2
du_'60''45'trans_436 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'trans_436 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
-- Data.Fin.Properties.<-cmp
d_'60''45'cmp_438 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_438 ~v0 v1 v2 = du_'60''45'cmp_438 v1 v2
du_'60''45'cmp_438 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''45'cmp_438 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> let v6 = coe du_'60''45'cmp_438 (coe v3) (coe v5) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v8
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v9
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.<-respˡ-≡
d_'60''45'resp'737''45''8801'_482 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'resp'737''45''8801'_482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'737''45''8801'_482 v6
du_'60''45'resp'737''45''8801'_482 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'resp'737''45''8801'_482 v0 = coe v0
-- Data.Fin.Properties.<-respʳ-≡
d_'60''45'resp'691''45''8801'_486 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'resp'691''45''8801'_486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'691''45''8801'_486 v6
du_'60''45'resp'691''45''8801'_486 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'resp'691''45''8801'_486 v0 = coe v0
-- Data.Fin.Properties.<-resp₂-≡
d_'60''45'resp'8322''45''8801'_490 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'8322''45''8801'_490 ~v0
  = du_'60''45'resp'8322''45''8801'_490
du_'60''45'resp'8322''45''8801'_490 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'8322''45''8801'_490
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Fin.Properties.<-irrelevant
d_'60''45'irrelevant_492 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_492 = erased
-- Data.Fin.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_494 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_494 ~v0
  = du_'60''45'isStrictPartialOrder_494
du_'60''45'isStrictPartialOrder_494 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''45'isStrictPartialOrder_494
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'60''45'trans_436 v1)
      (coe du_'60''45'resp'8322''45''8801'_490)
-- Data.Fin.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_496 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''45'isStrictTotalOrder_496 ~v0
  = du_'60''45'isStrictTotalOrder_496
du_'60''45'isStrictTotalOrder_496 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''45'isStrictTotalOrder_496
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe du_'60''45'isStrictPartialOrder_494) (coe du_'60''45'cmp_438)
-- Data.Fin.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_498 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'60''45'strictPartialOrder_498 ~v0
  = du_'60''45'strictPartialOrder_498
du_'60''45'strictPartialOrder_498 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_'60''45'strictPartialOrder_498
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      (coe du_'60''45'isStrictPartialOrder_494)
-- Data.Fin.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_502 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_'60''45'strictTotalOrder_502 ~v0
  = du_'60''45'strictTotalOrder_502
du_'60''45'strictTotalOrder_502 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
du_'60''45'strictTotalOrder_502
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      (coe du_'60''45'isStrictTotalOrder_496)
-- Data.Fin.Properties.i<1+i
d_i'60'1'43'i_508 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_i'60'1'43'i_508 ~v0 v1 = du_i'60'1'43'i_508 v1
du_i'60'1'43'i_508 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_i'60'1'43'i_508 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
-- Data.Fin.Properties.<⇒≢
d_'60''8658''8802'_510 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_510 = erased
-- Data.Fin.Properties.≤∧≢⇒<
d_'8804''8743''8802''8658''60'_514 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8743''8802''8658''60'_514 ~v0 v1 v2 ~v3 ~v4
  = du_'8804''8743''8802''8658''60'_514 v1 v2
du_'8804''8743''8802''8658''60'_514 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8743''8802''8658''60'_514 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_'8804''8743''8802''8658''60'_514 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.toℕ-inject
d_toℕ'45'inject_532 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inject_532 = erased
-- Data.Fin.Properties.fromℕ≢inject₁
d_fromℕ'8802'inject'8321'_540 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fromℕ'8802'inject'8321'_540 = erased
-- Data.Fin.Properties.inject₁-injective
d_inject'8321''45'injective_546 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8321''45'injective_546 = erased
-- Data.Fin.Properties.toℕ-inject₁
d_toℕ'45'inject'8321'_558 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inject'8321'_558 = erased
-- Data.Fin.Properties.toℕ-inject₁-≢
d_toℕ'45'inject'8321''45''8802'_564 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_toℕ'45'inject'8321''45''8802'_564 = erased
-- Data.Fin.Properties.inject₁ℕ<
d_inject'8321'ℕ'60'_570 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_inject'8321'ℕ'60'_570 ~v0 v1 = du_inject'8321'ℕ'60'_570 v1
du_inject'8321'ℕ'60'_570 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_inject'8321'ℕ'60'_570 v0 = coe du_toℕ'60'n_156 (coe v0)
-- Data.Fin.Properties.inject₁ℕ≤
d_inject'8321'ℕ'8804'_580 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_inject'8321'ℕ'8804'_580 ~v0 v1 = du_inject'8321'ℕ'8804'_580 v1
du_inject'8321'ℕ'8804'_580 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_inject'8321'ℕ'8804'_580 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
      (coe du_inject'8321'ℕ'60'_570 (coe v0))
-- Data.Fin.Properties.≤̄⇒inject₁<
d_'8804''772''8658'inject'8321''60'_582 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''772''8658'inject'8321''60'_582 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8804''772''8658'inject'8321''60'_582 v4
du_'8804''772''8658'inject'8321''60'_582 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''772''8658'inject'8321''60'_582 v0
  = coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v0
-- Data.Fin.Properties.ℕ<⇒inject₁<
d_ℕ'60''8658'inject'8321''60'_596 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ℕ'60''8658'inject'8321''60'_596 ~v0 v1 ~v2 v3
  = du_ℕ'60''8658'inject'8321''60'_596 v1 v3
du_ℕ'60''8658'inject'8321''60'_596 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ℕ'60''8658'inject'8321''60'_596 v0 v1
  = coe
      seq (coe v0)
      (coe
         du_'8804''772''8658'inject'8321''60'_582
         (coe
            MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v1)))
-- Data.Fin.Properties.i≤inject₁[j]⇒i≤1+j
d_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_602 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_602 ~v0 v1 ~v2 v3
                                                      v4
  = du_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_602 v1 v3 v4
du_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_602 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_602 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe
                   MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.inject!-injective
d_inject'33''45'injective_614 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'33''45'injective_614 = erased
-- Data.Fin.Properties.inject!-<
d_inject'33''45''60'_634 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_inject'33''45''60'_634 ~v0 v1 v2
  = du_inject'33''45''60'_634 v1 v2
du_inject'33''45''60'_634 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_inject'33''45''60'_634 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_inject'33''45''60'_634 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.toℕ-lower₁
d_toℕ'45'lower'8321'_650 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'lower'8321'_650 = erased
-- Data.Fin.Properties.lower₁-injective
d_lower'8321''45'injective_668 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'8321''45'injective_668 = erased
-- Data.Fin.Properties.inject₁-lower₁
d_inject'8321''45'lower'8321'_692 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8321''45'lower'8321'_692 = erased
-- Data.Fin.Properties.lower₁-inject₁′
d_lower'8321''45'inject'8321''8242'_708 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'8321''45'inject'8321''8242'_708 = erased
-- Data.Fin.Properties.lower₁-inject₁
d_lower'8321''45'inject'8321'_716 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'8321''45'inject'8321'_716 = erased
-- Data.Fin.Properties.lower₁-irrelevant
d_lower'8321''45'irrelevant_726 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'8321''45'irrelevant_726 = erased
-- Data.Fin.Properties.inject₁≡⇒lower₁≡
d_inject'8321''8801''8658'lower'8321''8801'_742 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8321''8801''8658'lower'8321''8801'_742 = erased
-- Data.Fin.Properties.lower-injective
d_lower'45'injective_756 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'45'injective_756 = erased
-- Data.Fin.Properties.toℕ-inject≤
d_toℕ'45'inject'8804'_774 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inject'8804'_774 = erased
-- Data.Fin.Properties.inject≤-refl
d_inject'8804''45'refl_786 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'refl_786 = erased
-- Data.Fin.Properties.inject≤-idempotent
d_inject'8804''45'idempotent_802 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'idempotent_802 = erased
-- Data.Fin.Properties.inject≤-trans
d_inject'8804''45'trans_820 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'trans_820 = erased
-- Data.Fin.Properties.inject≤-injective
d_inject'8804''45'injective_832 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'injective_832 = erased
-- Data.Fin.Properties.inject≤-irrelevant
d_inject'8804''45'irrelevant_848 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'irrelevant_848 = erased
-- Data.Fin.Properties.pred<
d_pred'60'_854 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'60'_854 ~v0 v1 ~v2 = du_pred'60'_854 v1
du_pred'60'_854 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pred'60'_854 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v2
        -> coe
             du_'8804''772''8658'inject'8321''60'_582
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.splitAt-↑ˡ
d_splitAt'45''8593''737'_866 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45''8593''737'_866 = erased
-- Data.Fin.Properties.splitAt⁻¹-↑ˡ
d_splitAt'8315''185''45''8593''737'_890 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'8315''185''45''8593''737'_890 = erased
-- Data.Fin.Properties.splitAt-↑ʳ
d_splitAt'45''8593''691'_924 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45''8593''691'_924 = erased
-- Data.Fin.Properties.splitAt⁻¹-↑ʳ
d_splitAt'8315''185''45''8593''691'_948 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'8315''185''45''8593''691'_948 = erased
-- Data.Fin.Properties.splitAt-join
d_splitAt'45'join_984 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45'join_984 = erased
-- Data.Fin.Properties.join-splitAt
d_join'45'splitAt_1004 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_join'45'splitAt_1004 = erased
-- Data.Fin.Properties.splitAt-<
d_splitAt'45''60'_1044 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45''60'_1044 = erased
-- Data.Fin.Properties.splitAt-≥
d_splitAt'45''8805'_1062 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45''8805'_1062 = erased
-- Data.Fin.Properties.+↔⊎
d_'43''8596''8846'_1072 ::
  Integer -> Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'43''8596''8846'_1072 v0 ~v1 = du_'43''8596''8846'_1072 v0
du_'43''8596''8846'_1072 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'43''8596''8846'_1072 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Fin.Base.du_splitAt_166 (coe v0))
      (coe MAlonzo.Code.Data.Fin.Base.du_join_180 (coe v0))
-- Data.Fin.Properties.remQuot-combine
d_remQuot'45'combine_1086 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_remQuot'45'combine_1086 = erased
-- Data.Fin.Properties.combine-remQuot
d_combine'45'remQuot_1116 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_combine'45'remQuot_1116 = erased
-- Data.Fin.Properties.toℕ-combine
d_toℕ'45'combine_1160 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'combine_1160 = erased
-- Data.Fin.Properties.combine-monoˡ-<
d_combine'45'mono'737''45''60'_1202 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_combine'45'mono'737''45''60'_1202 ~v0 v1 v2 v3 v4 v5 v6
  = du_combine'45'mono'737''45''60'_1202 v1 v2 v3 v4 v5 v6
du_combine'45'mono'737''45''60'_1202 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_combine'45'mono'737''45''60'_1202 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
      (coe
         MAlonzo.Code.Data.Fin.Base.du_toℕ_18
         (coe
            MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v1)
            (coe v3)))
      (coe
         MAlonzo.Code.Data.Fin.Base.du_toℕ_18
         (coe
            MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
            (coe v4)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
         (\ v6 v7 v8 v9 v10 -> v10)
         (coe
            MAlonzo.Code.Data.Fin.Base.du_toℕ_18
            (coe
               MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v1)
               (coe v3)))
         (addInt
            (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v3))
            (coe
               mulInt (coe v0)
               (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))))
         (coe
            MAlonzo.Code.Data.Fin.Base.du_toℕ_18
            (coe
               MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
               (coe v4)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_314
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (\ v6 v7 v8 v9 v10 ->
                  coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 v7 v9 v10)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (\ v6 v7 v8 v9 v10 ->
                  coe
                    MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134 v9
                    v10))
            (addInt
               (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v3))
               (coe
                  mulInt (coe v0)
                  (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))))
            (addInt
               (coe
                  mulInt (coe v0)
                  (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1)))
               (coe v0))
            (coe
               MAlonzo.Code.Data.Fin.Base.du_toℕ_18
               (coe
                  MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                  (coe v4)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
               (\ v6 v7 v8 v9 v10 -> v10)
               (addInt
                  (coe
                     mulInt (coe v0)
                     (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1)))
                  (coe v0))
               (addInt
                  (coe
                     mulInt (coe v0)
                     (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1)))
                  (coe v0))
               (coe
                  MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                  (coe
                     MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                     (coe v4)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                  (\ v6 v7 v8 v9 v10 -> v10)
                  (addInt
                     (coe
                        mulInt (coe v0)
                        (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1)))
                     (coe v0))
                  (addInt
                     (coe
                        mulInt (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
                        (coe v0))
                     (coe v0))
                  (coe
                     MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                     (coe
                        MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                        (coe v4)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                     (\ v6 v7 v8 v9 v10 -> v10)
                     (addInt
                        (coe
                           mulInt (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
                           (coe v0))
                        (coe v0))
                     (mulInt
                        (coe v0)
                        (coe
                           addInt (coe (1 :: Integer))
                           (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))))
                     (coe
                        MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                        (coe
                           MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                           (coe v4)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                           (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                           (\ v6 v7 v8 v9 v10 ->
                              coe
                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v9
                                v10))
                        (mulInt
                           (coe v0)
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))))
                        (mulInt
                           (coe v0) (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)))
                        (coe
                           MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                           (coe
                              MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                              (coe v4)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                              (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                              (\ v6 v7 v8 v9 v10 ->
                                 coe
                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                   v9 v10))
                           (mulInt
                              (coe v0) (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)))
                           (addInt
                              (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v4))
                              (coe
                                 mulInt (coe v0)
                                 (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2))))
                           (coe
                              MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                                 (coe v4)))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                              (\ v6 v7 v8 v9 v10 -> v10)
                              (addInt
                                 (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v4))
                                 (coe
                                    mulInt (coe v0)
                                    (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2))))
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                 (coe
                                    MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                 (coe
                                    MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                                 (coe
                                    MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                                       (coe v4))))
                              erased)
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
                              (coe
                                 mulInt (coe v0)
                                 (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)))))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.d_'42''45'mono'691''45''8804'_4224
                           v0
                           (addInt
                              (coe (1 :: Integer))
                              (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1)))
                           (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)) v5))
                     erased)
                  erased)
               erased)
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
               (coe
                  mulInt (coe v0)
                  (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1)))
               (coe du_toℕ'60'n_156 (coe v3))))
         erased)
-- Data.Fin.Properties.combine-injectiveˡ
d_combine'45'injective'737'_1232 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_combine'45'injective'737'_1232 = erased
-- Data.Fin.Properties.combine-injectiveʳ
d_combine'45'injective'691'_1292 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_combine'45'injective'691'_1292 = erased
-- Data.Fin.Properties.combine-injective
d_combine'45'injective_1324 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'injective_1324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_combine'45'injective_1324
du_combine'45'injective_1324 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'injective_1324
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Fin.Properties.combine-surjective
d_combine'45'surjective_1342 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'surjective_1342 ~v0 v1 v2
  = du_combine'45'surjective_1342 v1 v2
du_combine'45'surjective_1342 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'surjective_1342 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe
                 MAlonzo.Code.Data.Fin.Base.du_quotRem_192 (coe v0) (coe v1)) in
    coe
      (let v3
             = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Data.Fin.Base.du_quotRem_192 (coe v0) (coe v1)) in
       coe
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                  (\ v4 v5 v6 -> v6)
                  (coe
                     MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                     (coe v3))
                  v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
                     erased
                     (coe
                        MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0) (coe v2)
                        (coe v3))
                     (coe
                        MAlonzo.Code.Data.Product.Base.du_uncurry_244
                        (coe MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0))
                        (coe MAlonzo.Code.Data.Fin.Base.du_remQuot_204 (coe v0) (coe v1)))
                     v1
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
                        erased
                        (coe
                           MAlonzo.Code.Data.Product.Base.du_uncurry_244
                           (coe MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0))
                           (coe MAlonzo.Code.Data.Fin.Base.du_remQuot_204 (coe v0) (coe v1)))
                        v1 v1
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494 erased
                           (coe v1))
                        erased)
                     erased)))))
-- Data.Fin.Properties.*↔×
d_'42''8596''215'_1364 ::
  Integer -> Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'42''8596''215'_1364 ~v0 v1 = du_'42''8596''215'_1364 v1
du_'42''8596''215'_1364 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'42''8596''215'_1364 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Fin.Base.du_remQuot_204 (coe v0))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (coe MAlonzo.Code.Data.Fin.Base.du_combine_222 (coe v0)))
-- Data.Fin.Properties.funToFin-finToFin
d_funToFin'45'finToFin_1370 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funToFin'45'finToFin_1370 = erased
-- Data.Fin.Properties.finToFun-funToFin
d_finToFun'45'funToFin_1386 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_finToFun'45'funToFin_1386 = erased
-- Data.Fin.Properties.^↔→
d_'94''8596''8594'_1412 ::
  Integer ->
  Integer ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'94''8596''8594'_1412 v0 v1 ~v2 = du_'94''8596''8594'_1412 v0 v1
du_'94''8596''8594'_1412 ::
  Integer -> Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'94''8596''8594'_1412 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe MAlonzo.Code.Data.Fin.Base.d_finToFun_238 (coe v0) (coe v1))
      (coe MAlonzo.Code.Data.Fin.Base.d_funToFin_254 (coe v1) (coe v0))
-- Data.Fin.Properties.lift-injective
d_lift'45'injective_1424 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'45'injective_1424 = erased
-- Data.Fin.Properties.<⇒≤pred
d_'60''8658''8804'pred_1448 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8658''8804'pred_1448 ~v0 v1 ~v2 v3 v4
  = du_'60''8658''8804'pred_1448 v1 v3 v4
du_'60''8658''8804'pred_1448 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''8658''8804'pred_1448 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             seq (coe v1)
             (case coe v2 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
                  -> coe seq (coe v6) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> coe
             seq (coe v1)
             (case coe v2 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7 -> coe v7
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.toℕ‿ℕ-
d_toℕ'8255'ℕ'45'_1466 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'8255'ℕ'45'_1466 = erased
-- Data.Fin.Properties.ℕ-ℕ≡toℕ‿ℕ-
d_ℕ'45'ℕ'8801'toℕ'8255'ℕ'45'_1478 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ℕ'45'ℕ'8801'toℕ'8255'ℕ'45'_1478 = erased
-- Data.Fin.Properties.nℕ-ℕi≤n
d_nℕ'45'ℕi'8804'n_1490 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nℕ'45'ℕi'8804'n_1490 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe
                MAlonzo.Code.Data.Fin.Base.d__ℕ'45'ℕ__372 (coe v0)
                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                   (\ v5 v6 v7 ->
                      coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v7))
                (MAlonzo.Code.Data.Fin.Base.d__ℕ'45'ℕ__372
                   (coe v0) (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3))
                v0
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                      (\ v5 v6 v7 v8 v9 ->
                         coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v8
                           v9))
                   (MAlonzo.Code.Data.Fin.Base.d__ℕ'45'ℕ__372 (coe v4) (coe v3)) v4 v0
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                         (\ v5 v6 v7 v8 v9 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v8
                              v9))
                      v4 v0 v0
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                         (coe v0))
                      (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988 (coe v4)))
                   (d_nℕ'45'ℕi'8804'n_1490 (coe v4) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.punchIn-injective
d_punchIn'45'injective_1508 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchIn'45'injective_1508 = erased
-- Data.Fin.Properties.punchInᵢ≢i
d_punchIn'7522''8802'i_1524 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_punchIn'7522''8802'i_1524 = erased
-- Data.Fin.Properties.punchIn-mono-≤
d_punchIn'45'mono'45''8804'_1536 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_punchIn'45'mono'45''8804'_1536 ~v0 v1 v2 v3 v4
  = du_punchIn'45'mono'45''8804'_1536 v1 v2 v3 v4
du_punchIn'45'mono'45''8804'_1536 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_punchIn'45'mono'45''8804'_1536 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe seq (coe v3) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12
                             -> coe
                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                  (coe
                                     du_punchIn'45'mono'45''8804'_1536 (coe v5) (coe v7) (coe v9)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.punchIn-cancel-≤
d_punchIn'45'cancel'45''8804'_1554 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_punchIn'45'cancel'45''8804'_1554 ~v0 v1 v2 v3 v4
  = du_punchIn'45'cancel'45''8804'_1554 v1 v2 v3 v4
du_punchIn'45'cancel'45''8804'_1554 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_punchIn'45'cancel'45''8804'_1554 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7 -> coe v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe seq (coe v3) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12
                             -> coe
                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                  (coe
                                     du_punchIn'45'cancel'45''8804'_1554 (coe v5) (coe v7) (coe v9)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.punchOut-cong
d_punchOut'45'cong_1576 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchOut'45'cong_1576 = erased
-- Data.Fin.Properties.punchOut-cong′
d_punchOut'45'cong'8242'_1610 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchOut'45'cong'8242'_1610 = erased
-- Data.Fin.Properties.punchOut-injective
d_punchOut'45'injective_1626 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchOut'45'injective_1626 = erased
-- Data.Fin.Properties.punchOut-mono-≤
d_punchOut'45'mono'45''8804'_1666 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_punchOut'45'mono'45''8804'_1666 ~v0 v1 v2 v3 ~v4 ~v5 v6
  = du_punchOut'45'mono'45''8804'_1666 v1 v2 v3 v6
du_punchOut'45'mono'45''8804'_1666 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_punchOut'45'mono'45''8804'_1666 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    seq (coe v3)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe
                    seq (coe v2)
                    (case coe v3 of
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9 -> coe v9
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe seq (coe v3) (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12
                             -> coe
                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                  (coe
                                     du_punchOut'45'mono'45''8804'_1666 (coe v5) (coe v7) (coe v9)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.punchOut-cancel-≤
d_punchOut'45'cancel'45''8804'_1688 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_punchOut'45'cancel'45''8804'_1688 ~v0 v1 v2 v3 ~v4 ~v5 v6
  = du_punchOut'45'cancel'45''8804'_1688 v1 v2 v3 v6
du_punchOut'45'cancel'45''8804'_1688 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_punchOut'45'cancel'45''8804'_1688 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                           erased
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v8
                      -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12
                             -> coe
                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                  (coe
                                     du_punchOut'45'cancel'45''8804'_1688 (coe v5) (coe v7) (coe v9)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.punchIn-punchOut
d_punchIn'45'punchOut_1708 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchIn'45'punchOut_1708 = erased
-- Data.Fin.Properties.punchOut-punchIn
d_punchOut'45'punchIn_1732 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchOut'45'punchIn_1732 = erased
-- Data.Fin.Properties.pinch-surjective
d_pinch'45'surjective_1748 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pinch'45'surjective_1748 ~v0 v1 v2
  = du_pinch'45'surjective_1748 v1 v2
du_pinch'45'surjective_1748 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pinch'45'surjective_1748 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) erased
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> case coe v0 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                       (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3))
                    erased
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_map_128
                    (coe MAlonzo.Code.Data.Fin.Base.C_suc_16) erased
                    (coe du_pinch'45'surjective_1748 (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties..extendedlambda8
d_'46'extendedlambda8_1750 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda8_1750 = erased
-- Data.Fin.Properties..extendedlambda9
d_'46'extendedlambda9_1754 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda9_1754 = erased
-- Data.Fin.Properties..extendedlambda10
d_'46'extendedlambda10_1760 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda10_1760 = erased
-- Data.Fin.Properties.pinch-mono-≤
d_pinch'45'mono'45''8804'_1766 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pinch'45'mono'45''8804'_1766 ~v0 v1 v2 v3 v4
  = du_pinch'45'mono'45''8804'_1766 v1 v2 v3 v4
du_pinch'45'mono'45''8804'_1766 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pinch'45'mono'45''8804'_1766 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe
                    seq (coe v2)
                    (coe MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
                      -> coe
                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                           (coe
                              du_pinch'45'mono'45''8804'_1766 (coe v5) (coe v7) (coe v9)
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v3)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.pinch-injective
d_pinch'45'injective_1798 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pinch'45'injective_1798 = erased
-- Data.Fin.Properties._.∀-cons
d_'8704''45'cons_1842 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  AgdaAny ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_'8704''45'cons_1842 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8704''45'cons_1842 v3 v4 v5
du_'8704''45'cons_1842 ::
  AgdaAny ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_'8704''45'cons_1842 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v0
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe v1 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties._.∀-cons-⇔
d_'8704''45'cons'45''8660'_1854 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_'8704''45'cons'45''8660'_1854 ~v0 ~v1 ~v2
  = du_'8704''45'cons'45''8660'_1854
du_'8704''45'cons'45''8660'_1854 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_'8704''45'cons'45''8660'_1854
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (coe du_'8704''45'cons_1842))
      (coe
         MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
         (coe (\ v0 -> coe v0 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            (\ v0 v1 -> coe v0 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v1))))
-- Data.Fin.Properties._.∃-here
d_'8707''45'here_1860 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8707''45'here_1860 ~v0 ~v1 ~v2 v3 = du_'8707''45'here_1860 v3
du_'8707''45'here_1860 ::
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8707''45'here_1860 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v0)
-- Data.Fin.Properties._.∃-there
d_'8707''45'there_1864 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8707''45'there_1864 ~v0 ~v1 ~v2 = du_'8707''45'there_1864
du_'8707''45'there_1864 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8707''45'there_1864
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe MAlonzo.Code.Data.Fin.Base.C_suc_16) (coe (\ v0 v1 -> v1))
-- Data.Fin.Properties._.∃-toSum
d_'8707''45'toSum_1866 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8707''45'toSum_1866 ~v0 ~v1 ~v2 v3 = du_'8707''45'toSum_1866 v3
du_'8707''45'toSum_1866 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8707''45'toSum_1866 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties._.⊎⇔∃
d_'8846''8660''8707'_1874 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_'8846''8660''8707'_1874 ~v0 ~v1 ~v2 = du_'8846''8660''8707'_1874
du_'8846''8660''8707'_1874 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_'8846''8660''8707'_1874
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
         (coe du_'8707''45'here_1860) (coe du_'8707''45'there_1864))
      (coe du_'8707''45'toSum_1866)
-- Data.Fin.Properties.decFinSubset
d_decFinSubset_1886 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decFinSubset_1886 v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_decFinSubset_1886 v0 v5 v6
du_decFinSubset_1886 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decFinSubset_1886 v0 v1 v2
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v4 = coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) in
              coe
                (let v5 = coe du_'8704''45'cons_1842 in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                    (coe
                                       MAlonzo.Code.Data.Product.Base.du_uncurry_244
                                       (coe
                                          (\ v8 v9 v10 ->
                                             coe v5 (\ v11 -> v8) (\ v11 -> coe v9 v11) v10)))
                                    (coe
                                       MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
                                       (coe
                                          (\ v8 ->
                                             coe
                                               v8 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                                                  (coe v7))))
                                       (coe
                                          (\ v8 v9 ->
                                             coe v8 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v9))))
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                       (coe
                                          v2 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                                             (coe v7)))
                                       (coe
                                          du_decFinSubset_1886 (coe v3)
                                          (coe
                                             (\ v8 ->
                                                coe
                                                  v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8)))
                                          (coe
                                             (\ v8 ->
                                                coe
                                                  v2
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8)))))
                             else coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                    (coe
                                       (\ v8 v9 ->
                                          coe
                                            v5
                                            (\ v10 ->
                                               coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                            (\ v10 -> coe v8 v10) v9))
                                    (coe
                                       (\ v8 v9 ->
                                          coe v8 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v9)))
                                    (coe
                                       du_decFinSubset_1886 (coe v3)
                                       (coe
                                          (\ v8 ->
                                             coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8)))
                                       (coe
                                          (\ v8 ->
                                             coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8))))
                      _ -> MAlonzo.RTE.mazUnreachableError)))
-- Data.Fin.Properties.any?
d_any'63'_1966 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_any'63'_1966 v0 ~v1 ~v2 v3 = du_any'63'_1966 v0 v3
du_any'63'_1966 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_any'63'_1966 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
                (coe du_'8846''8660''8707'_1874)
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                   (coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                   (coe
                      du_any'63'_1966 (coe v2)
                      (coe
                         (\ v3 -> coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3))))))
-- Data.Fin.Properties.all?
d_all'63'_1984 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_all'63'_1984 v0 ~v1 ~v2 v3 = du_all'63'_1984 v0 v3
du_all'63'_1984 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_all'63'_1984 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (coe
         (\ v2 v3 -> coe v2 v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      (coe (\ v2 v3 v4 -> coe v2 v3))
      (coe
         du_decFinSubset_1886 (coe v0)
         (\ v2 -> coe MAlonzo.Code.Relation.Unary.Properties.du_U'63'_34)
         (coe (\ v2 v3 -> coe v1 v2)))
-- Data.Fin.Properties.¬∀⟶∃¬-smallest
d_'172''8704''10230''8707''172''45'smallest_2026 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  ((MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'172''8704''10230''8707''172''45'smallest_2026 v0 ~v1 ~v2 v3 ~v4
  = du_'172''8704''10230''8707''172''45'smallest_2026 v0 v3
du_'172''8704''10230''8707''172''45'smallest_2026 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'172''8704''10230''8707''172''45'smallest_2026 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v3 = coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                     -> if coe v4
                          then coe
                                 MAlonzo.Code.Data.Product.Base.du_map_128
                                 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
                                 (coe
                                    (\ v6 ->
                                       coe
                                         MAlonzo.Code.Data.Product.Base.du_map_128
                                         (coe (\ v7 -> v7))
                                         (coe
                                            (\ v7 ->
                                               coe
                                                 du_'8704''45'cons_1842
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                                                    (coe v5))))))
                                 (coe
                                    du_'172''8704''10230''8707''172''45'smallest_2026 (coe v2)
                                    (coe
                                       (\ v6 ->
                                          coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v6))))
                          else coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v5))
                                    erased)
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Fin.Properties.¬∀⟶∃¬
d_'172''8704''10230''8707''172'_2076 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  ((MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'172''8704''10230''8707''172'_2076 v0 ~v1 ~v2 v3 ~v4
  = du_'172''8704''10230''8707''172'_2076 v0 v3
du_'172''8704''10230''8707''172'_2076 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'172''8704''10230''8707''172'_2076 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128 (coe (\ v2 -> v2))
      (coe
         (\ v2 v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         du_'172''8704''10230''8707''172''45'smallest_2026 (coe v0)
         (coe v1))
-- Data.Fin.Properties.pigeonhole
d_pigeonhole_2092 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pigeonhole_2092 ~v0 v1 v2 v3 = du_pigeonhole_2092 v1 v2 v3
du_pigeonhole_2092 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pigeonhole_2092 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
        -> case coe v5 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
               -> let v9 = subInt (coe v0) (coe (2 :: Integer)) in
                  coe
                    (let v10
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               (coe
                                  MAlonzo.Code.Function.Bundles.d_to_1868
                                  (coe du_'8846''8660''8707'_1874))
                               (coe
                                  MAlonzo.Code.Function.Bundles.d_from_1870
                                  (coe du_'8846''8660''8707'_1874))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                                  (coe
                                     du__'8799'__50
                                     (coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                     (coe
                                        v2
                                        (coe
                                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                  (coe
                                     du_any'63'_1966 (coe v9)
                                     (coe
                                        (\ v10 ->
                                           coe
                                             du__'8799'__50
                                             (coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                             (coe
                                                v2
                                                (coe
                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                   (coe
                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                      v10))))))) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                            -> if coe v11
                                 then case coe v12 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                          -> case coe v13 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Data.Fin.Base.C_suc_16 v14)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
                                                            (coe v15)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v12)
                                        (let v13
                                               = coe
                                                   du_pigeonhole_2092
                                                   (coe subInt (coe v0) (coe (1 :: Integer)))
                                                   (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8)
                                                   (coe
                                                      (\ v13 ->
                                                         coe
                                                           MAlonzo.Code.Data.Fin.Base.du_punchOut_396
                                                           (coe
                                                              v2
                                                              (coe
                                                                 MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                                           (coe
                                                              v2
                                                              (coe
                                                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                 v13)))) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                -> case coe v15 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                       -> case coe v17 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                      v14)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                         v16)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                            v18)
                                                                         erased))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.injective⇒≤
d_injective'8658''8804'_2140 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_injective'8658''8804'_2140 v0 v1 ~v2 ~v3
  = du_injective'8658''8804'_2140 v0 v1
du_injective'8658''8804'_2140 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_injective'8658''8804'_2140 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe du_injective'8658''8804'_2140 (coe v2) (coe v3))))
-- Data.Fin.Properties.<⇒notInjective
d_'60''8658'notInjective_2154 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658'notInjective_2154 = erased
-- Data.Fin.Properties.ℕ→Fin-notInjective
d_ℕ'8594'Fin'45'notInjective_2162 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ℕ'8594'Fin'45'notInjective_2162 = erased
-- Data.Fin.Properties.cantor-schröder-bernstein
d_cantor'45'schröder'45'bernstein_2172 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cantor'45'schröder'45'bernstein_2172 = erased
-- Data.Fin.Properties.injective⇒existsPivot
d_injective'8658'existsPivot_2184 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_injective'8658'existsPivot_2184 v0 ~v1 v2 ~v3 v4
  = du_injective'8658'existsPivot_2184 v0 v2 v4
du_injective'8658'existsPivot_2184 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_injective'8658'existsPivot_2184 v0 v1 v2
  = let v3
          = coe
              du_any'63'_1966 (coe v0)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                      (coe du__'8804''63'__396 (coe v3) (coe v2))
                      (coe du__'8804''63'__396 (coe v2) (coe v1 v3)))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6 -> coe v6
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                          erased)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Properties._.fj<i
d_fj'60'i_2220 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fj'60'i_2220 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 = du_fj'60'i_2220 v2 v3 v6
du_fj'60'i_2220 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fj'60'i_2220 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v3 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                   (coe
                      addInt (coe (1 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                         (coe
                            v0
                            (coe
                               MAlonzo.Code.Data.Fin.Base.du_inject'33'_114
                               (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v1) (coe v2))))))
              (coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                          (coe
                             v0
                             (coe
                                MAlonzo.Code.Data.Fin.Base.du_inject'33'_114
                                (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v1) (coe v2)))))
                    (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1)))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6 -> coe v6
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                          erased)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Properties._.f∘inject!
d_f'8728'inject'33'_2236 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_f'8728'inject'33'_2236 ~v0 ~v1 v2 v3 ~v4 ~v5 v6
  = du_f'8728'inject'33'_2236 v2 v3 v6
du_f'8728'inject'33'_2236 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_f'8728'inject'33'_2236 v0 v1 v2
  = coe
      v0
      (coe
         MAlonzo.Code.Data.Fin.Base.du_inject'33'_114
         (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v1) (coe v2))
-- Data.Fin.Properties._.f∘inject!-injective
d_f'8728'inject'33''45'injective_2240 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'8728'inject'33''45'injective_2240 = erased
-- Data.Fin.Properties._.sequence
d_sequence_2294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
d_sequence_2294 ~v0 ~v1 v2 v3 ~v4 v5 = du_sequence_2294 v2 v3 v5
du_sequence_2294 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
du_sequence_2294 v0 v1 v2
  = case coe v1 of
      0 -> coe MAlonzo.Code.Effect.Applicative.d_pure_32 v0 erased erased
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34 v0 erased
                erased
                (coe
                   MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
                   (MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v0)) erased
                   erased (coe du_'8704''45'cons_1842)
                   (coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                (coe
                   du_sequence_2294 (coe v0) (coe v3)
                   (coe
                      (\ v4 -> coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v4)))))
-- Data.Fin.Properties._.sequence⁻¹
d_sequence'8315''185'_2330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny
d_sequence'8315''185'_2330 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_sequence'8315''185'_2330 v2 v5 v6
du_sequence'8315''185'_2330 ::
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_sequence'8315''185'_2330 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30 v0 erased erased
      (\ v3 -> coe v3 v2) v1
-- Data.Fin.Properties._._._≈_
d__'8776'__2354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__2354 = erased
-- Data.Fin.Properties._.inj⇒≟
d_inj'8658''8799'_2376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inj'8658''8799'_2376 ~v0 ~v1 ~v2 ~v3 v4
  = du_inj'8658''8799'_2376 v4
du_inj'8658''8799'_2376 ::
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_inj'8658''8799'_2376 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.du_via'45'injection_180
      (coe v0) (coe du__'8799'__50)
-- Data.Fin.Properties._.inj⇒decSetoid
d_inj'8658'decSetoid_2378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_inj'8658'decSetoid_2378 ~v0 ~v1 ~v2 v3 v4
  = du_inj'8658'decSetoid_2378 v3 v4
du_inj'8658'decSetoid_2378 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_inj'8658'decSetoid_2378 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0))
         (coe du_inj'8658''8799'_2376 (coe v1)))
-- Data.Fin.Properties.opposite-prop
d_opposite'45'prop_2382 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'prop_2382 = erased
-- Data.Fin.Properties.opposite-involutive
d_opposite'45'involutive_2394 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'involutive_2394 = erased
-- Data.Fin.Properties.opposite-suc
d_opposite'45'suc_2408 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'suc_2408 = erased
-- Data.Fin.Properties.inject+-raise-splitAt
d_inject'43''45'raise'45'splitAt_2418 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'43''45'raise'45'splitAt_2418 = erased
-- Data.Fin.Properties.toℕ-raise
d_toℕ'45'raise_2420 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'raise_2420 = erased
-- Data.Fin.Properties.toℕ-inject+
d_toℕ'45'inject'43'_2428 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inject'43'_2428 = erased
-- Data.Fin.Properties.splitAt-inject+
d_splitAt'45'inject'43'_2440 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45'inject'43'_2440 = erased
-- Data.Fin.Properties.splitAt-raise
d_splitAt'45'raise_2454 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45'raise_2454 = erased
-- Data.Fin.Properties.Fin0↔⊥
d_Fin0'8596''8869'_2456 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_Fin0'8596''8869'_2456 = coe d_0'8596''8869'_24
-- Data.Fin.Properties.eq?
d_eq'63'_2458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eq'63'_2458 ~v0 ~v1 ~v2 = du_eq'63'_2458
du_eq'63'_2458 ::
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_eq'63'_2458 = coe du_inj'8658''8799'_2376
-- Data.Fin.Properties.z≺s
d_z'8826's_2462 ::
  Integer -> MAlonzo.Code.Data.Fin.Base.T__'8826'__548
d_z'8826's_2462 ~v0 = du_z'8826's_2462
du_z'8826's_2462 :: MAlonzo.Code.Data.Fin.Base.T__'8826'__548
du_z'8826's_2462
  = coe
      MAlonzo.Code.Data.Fin.Base.C__'8827'toℕ__554
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- Data.Fin.Properties.s≺s
d_s'8826's_2468 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548
d_s'8826's_2468 ~v0 ~v1 v2 = du_s'8826's_2468 v2
du_s'8826's_2468 ::
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548
du_s'8826's_2468 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C__'8827'toℕ__554 v2
        -> coe
             MAlonzo.Code.Data.Fin.Base.C__'8827'toℕ__554
             (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.<⇒≺
d_'60''8658''8826'_2474 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548
d_'60''8658''8826'_2474 v0 ~v1 v2 = du_'60''8658''8826'_2474 v0 v2
du_'60''8658''8826'_2474 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548
du_'60''8658''8826'_2474 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
               -> coe seq (coe v4) (coe du_z'8826's_2462)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe
                       du_s'8826's_2468 (coe du_'60''8658''8826'_2474 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Properties.≺⇒<
d_'8826''8658''60'_2480 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8826''8658''60'_2480 ~v0 ~v1 v2 = du_'8826''8658''60'_2480 v2
du_'8826''8658''60'_2480 ::
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8826''8658''60'_2480 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C__'8827'toℕ__554 v2
        -> coe du_toℕ'60'n_156 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.≺⇒<′
d_'8826''8658''60''8242'_2486 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
d_'8826''8658''60''8242'_2486 ~v0 v1 v2
  = du_'8826''8658''60''8242'_2486 v1 v2
du_'8826''8658''60''8242'_2486 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342
du_'8826''8658''60''8242'_2486 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''60''8242'_6256
      (coe v0) (coe du_'8826''8658''60'_2480 (coe v1))
-- Data.Fin.Properties.<′⇒≺
d_'60''8242''8658''8826'_2490 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548
d_'60''8242''8658''8826'_2490 v0 ~v1 v2
  = du_'60''8242''8658''8826'_2490 v0 v2
du_'60''8242''8658''8826'_2490 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__548
du_'60''8242''8658''8826'_2490 v0 v1
  = coe
      du_'60''8658''8826'_2474 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8242''8658''60'_6260
         (coe v0) (coe v1))
