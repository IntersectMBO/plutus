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

module MAlonzo.Code.Data.Fin.Properties where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Definitions.RawMagma qualified
import MAlonzo.Code.Data.Empty qualified
import MAlonzo.Code.Data.Fin.Base qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Nat.Base qualified
import MAlonzo.Code.Data.Nat.Properties qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Effect.Applicative qualified
import MAlonzo.Code.Effect.Functor qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Core qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Negation.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.Code.Relation.Unary.Properties qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
      MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Fin.Properties.0↔⊥
d_0'8596''8869'_24 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_0'8596''8869'_24
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366 erased
      erased
-- Data.Fin.Properties.1↔⊤
d_1'8596''8868'_26 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_1'8596''8868'_26
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         (\ v0 -> seq (coe v0) (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Data.Fin.Properties..extendedlambda3
d_'46'extendedlambda3_34 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda3_34 = erased
-- Data.Fin.Properties.2↔Bool
d_2'8596'Bool_36 :: MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_2'8596'Bool_36
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
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
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    erased erased (coe du__'8799'__50 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.≡-isDecEquivalence
d_'8801''45'isDecEquivalence_60 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8801''45'isDecEquivalence_60 ~v0
  = du_'8801''45'isDecEquivalence_60
du_'8801''45'isDecEquivalence_60 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_'8801''45'isDecEquivalence_60
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe du__'8799'__50)
-- Data.Fin.Properties.≡-preorder
d_'8801''45'preorder_62 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8801''45'preorder_62 ~v0 = du_'8801''45'preorder_62
du_'8801''45'preorder_62 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_'8801''45'preorder_62
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_preorder_414
-- Data.Fin.Properties.≡-setoid
d_'8801''45'setoid_66 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8801''45'setoid_66 ~v0 = du_'8801''45'setoid_66
du_'8801''45'setoid_66 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_'8801''45'setoid_66
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Fin.Properties.≡-decSetoid
d_'8801''45'decSetoid_70 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8801''45'decSetoid_70 ~v0 = du_'8801''45'decSetoid_70
du_'8801''45'decSetoid_70 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
du_'8801''45'decSetoid_70
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1389
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
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'pred_5664
      (coe du_toℕ'60'n_156 (coe v0))
-- Data.Fin.Properties.toℕ-mono-<
d_toℕ'45'mono'45''60'_182 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'mono'45''60'_182 ~v0 ~v1 ~v2 ~v3 v4
  = du_toℕ'45'mono'45''60'_182 v4
du_toℕ'45'mono'45''60'_182 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'45'mono'45''60'_182 v0 = coe v0
-- Data.Fin.Properties.toℕ-mono-≤
d_toℕ'45'mono'45''8804'_186 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'mono'45''8804'_186 ~v0 ~v1 ~v2 ~v3 v4
  = du_toℕ'45'mono'45''8804'_186 v4
du_toℕ'45'mono'45''8804'_186 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'45'mono'45''8804'_186 v0 = coe v0
-- Data.Fin.Properties.toℕ-cancel-≤
d_toℕ'45'cancel'45''8804'_190 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'cancel'45''8804'_190 ~v0 ~v1 ~v2 ~v3 v4
  = du_toℕ'45'cancel'45''8804'_190 v4
du_toℕ'45'cancel'45''8804'_190 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_toℕ'45'cancel'45''8804'_190 v0 = coe v0
-- Data.Fin.Properties.toℕ-cancel-<
d_toℕ'45'cancel'45''60'_194 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_toℕ'45'cancel'45''60'_194 ~v0 ~v1 ~v2 ~v3 v4
  = du_toℕ'45'cancel'45''60'_194 v4
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
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fromℕ'60''8801'fromℕ'60''8243'_286 = erased
-- Data.Fin.Properties.toℕ-fromℕ<″
d_toℕ'45'fromℕ'60''8243'_296 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
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
-- Data.Fin.Properties.≤-reflexive
d_'8804''45'reflexive_362 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'reflexive_362 ~v0 v1 ~v2 ~v3
  = du_'8804''45'reflexive_362 v1
du_'8804''45'reflexive_362 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'reflexive_362 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
-- Data.Fin.Properties.≤-refl
d_'8804''45'refl_364 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'refl_364 ~v0 v1 = du_'8804''45'refl_364 v1
du_'8804''45'refl_364 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'refl_364 v0 = coe du_'8804''45'reflexive_362 (coe v0)
-- Data.Fin.Properties.≤-trans
d_'8804''45'trans_366 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'trans_366 ~v0 ~v1 ~v2 ~v3 = du_'8804''45'trans_366
du_'8804''45'trans_366 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'trans_366
  = coe MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2784
-- Data.Fin.Properties.≤-antisym
d_'8804''45'antisym_368 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_368 = erased
-- Data.Fin.Properties.≤-total
d_'8804''45'total_374 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_374 ~v0 v1 v2 = du_'8804''45'total_374 v1 v2
du_'8804''45'total_374 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''45'total_374 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'total_2790
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
-- Data.Fin.Properties.≤-irrelevant
d_'8804''45'irrelevant_380 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_380 = erased
-- Data.Fin.Properties._≤?_
d__'8804''63'__382 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__382 ~v0 ~v1 v2 v3 = du__'8804''63'__382 v2 v3
du__'8804''63'__382 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8804''63'__382 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
-- Data.Fin.Properties._<?_
d__'60''63'__388 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__388 ~v0 ~v1 v2 v3 = du__'60''63'__388 v2 v3
du__'60''63'__388 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'60''63'__388 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.d__'8804''63'__2802
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0)))
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
-- Data.Fin.Properties.≤-isPreorder
d_'8804''45'isPreorder_394 ::
  Integer -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_394 ~v0 = du_'8804''45'isPreorder_394
du_'8804''45'isPreorder_394 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_'8804''45'isPreorder_394
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_362 v0)
      (\ v0 v1 v2 -> coe du_'8804''45'trans_366)
-- Data.Fin.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_396 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8804''45'isPartialOrder_396 ~v0
  = du_'8804''45'isPartialOrder_396
du_'8804''45'isPartialOrder_396 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8804''45'isPartialOrder_396
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe du_'8804''45'isPreorder_394) erased
-- Data.Fin.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_398 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8804''45'isTotalOrder_398 ~v0 = du_'8804''45'isTotalOrder_398
du_'8804''45'isTotalOrder_398 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_'8804''45'isTotalOrder_398
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_20555
      (coe du_'8804''45'isPartialOrder_396) (coe du_'8804''45'total_374)
-- Data.Fin.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_400 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8804''45'isDecTotalOrder_400 ~v0
  = du_'8804''45'isDecTotalOrder_400
du_'8804''45'isDecTotalOrder_400 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
du_'8804''45'isDecTotalOrder_400
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22695
      (coe du_'8804''45'isTotalOrder_398) (coe du__'8799'__50)
      (coe du__'8804''63'__382)
-- Data.Fin.Properties.≤-preorder
d_'8804''45'preorder_402 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8804''45'preorder_402 ~v0 = du_'8804''45'preorder_402
du_'8804''45'preorder_402 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_'8804''45'preorder_402
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      (coe du_'8804''45'isPreorder_394)
-- Data.Fin.Properties.≤-poset
d_'8804''45'poset_406 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8804''45'poset_406 ~v0 = du_'8804''45'poset_406
du_'8804''45'poset_406 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_'8804''45'poset_406
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (coe du_'8804''45'isPartialOrder_396)
-- Data.Fin.Properties.≤-totalOrder
d_'8804''45'totalOrder_410 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_'8804''45'totalOrder_410 ~v0 = du_'8804''45'totalOrder_410
du_'8804''45'totalOrder_410 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
du_'8804''45'totalOrder_410
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_15747
      (coe du_'8804''45'isTotalOrder_398)
-- Data.Fin.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_414 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_'8804''45'decTotalOrder_414 ~v0 = du_'8804''45'decTotalOrder_414
du_'8804''45'decTotalOrder_414 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
du_'8804''45'decTotalOrder_414
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17849
      (coe du_'8804''45'isDecTotalOrder_400)
-- Data.Fin.Properties.<-irrefl
d_'60''45'irrefl_418 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_418 = erased
-- Data.Fin.Properties.<-asym
d_'60''45'asym_420 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_420 = erased
-- Data.Fin.Properties.<-trans
d_'60''45'trans_422 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans_422 ~v0 ~v1 v2 ~v3 = du_'60''45'trans_422 v2
du_'60''45'trans_422 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'trans_422 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_2980
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
-- Data.Fin.Properties.<-cmp
d_'60''45'cmp_424 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_424 ~v0 v1 v2 = du_'60''45'cmp_424 v1 v2
du_'60''45'cmp_424 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''45'cmp_424 v0 v1
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
               -> let v6 = coe du_'60''45'cmp_424 (coe v3) (coe v5) in
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
d_'60''45'resp'737''45''8801'_468 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'resp'737''45''8801'_468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'737''45''8801'_468 v6
du_'60''45'resp'737''45''8801'_468 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'resp'737''45''8801'_468 v0 = coe v0
-- Data.Fin.Properties.<-respʳ-≡
d_'60''45'resp'691''45''8801'_472 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'resp'691''45''8801'_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'resp'691''45''8801'_472 v6
du_'60''45'resp'691''45''8801'_472 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'resp'691''45''8801'_472 v0 = coe v0
-- Data.Fin.Properties.<-resp₂-≡
d_'60''45'resp'8322''45''8801'_476 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'8322''45''8801'_476 ~v0
  = du_'60''45'resp'8322''45''8801'_476
du_'60''45'resp'8322''45''8801'_476 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'8322''45''8801'_476
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Fin.Properties.<-irrelevant
d_'60''45'irrelevant_478 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_478 = erased
-- Data.Fin.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_480 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_480 ~v0
  = du_'60''45'isStrictPartialOrder_480
du_'60''45'isStrictPartialOrder_480 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''45'isStrictPartialOrder_480
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'60''45'trans_422 v1)
      (coe du_'60''45'resp'8322''45''8801'_476)
-- Data.Fin.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_482 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder_482 ~v0
  = du_'60''45'isStrictTotalOrder_482
du_'60''45'isStrictTotalOrder_482 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''45'isStrictTotalOrder_482
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe du_'60''45'isStrictPartialOrder_480) (coe du_'60''45'cmp_424)
-- Data.Fin.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_484 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_484 ~v0
  = du_'60''45'strictPartialOrder_484
du_'60''45'strictPartialOrder_484 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_'60''45'strictPartialOrder_484
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11097
      (coe du_'60''45'isStrictPartialOrder_480)
-- Data.Fin.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_488 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder_488 ~v0
  = du_'60''45'strictTotalOrder_488
du_'60''45'strictTotalOrder_488 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
du_'60''45'strictTotalOrder_488
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_21059
      (coe du_'60''45'isStrictTotalOrder_482)
-- Data.Fin.Properties.i<1+i
d_i'60'1'43'i_494 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_i'60'1'43'i_494 ~v0 v1 = du_i'60'1'43'i_494 v1
du_i'60'1'43'i_494 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_i'60'1'43'i_494 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3078
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0))
-- Data.Fin.Properties.<⇒≢
d_'60''8658''8802'_496 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_496 = erased
-- Data.Fin.Properties.≤∧≢⇒<
d_'8804''8743''8802''8658''60'_500 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8743''8802''8658''60'_500 ~v0 v1 v2 ~v3 ~v4
  = du_'8804''8743''8802''8658''60'_500 v1 v2
du_'8804''8743''8802''8658''60'_500 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8743''8802''8658''60'_500 v0 v1
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
                    (coe du_'8804''8743''8802''8658''60'_500 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.toℕ-inject
d_toℕ'45'inject_518 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inject_518 = erased
-- Data.Fin.Properties.fromℕ≢inject₁
d_fromℕ'8802'inject'8321'_526 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fromℕ'8802'inject'8321'_526 = erased
-- Data.Fin.Properties.inject₁-injective
d_inject'8321''45'injective_532 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8321''45'injective_532 = erased
-- Data.Fin.Properties.toℕ-inject₁
d_toℕ'45'inject'8321'_544 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inject'8321'_544 = erased
-- Data.Fin.Properties.toℕ-inject₁-≢
d_toℕ'45'inject'8321''45''8802'_550 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_toℕ'45'inject'8321''45''8802'_550 = erased
-- Data.Fin.Properties.inject₁ℕ<
d_inject'8321'ℕ'60'_556 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_inject'8321'ℕ'60'_556 ~v0 v1 = du_inject'8321'ℕ'60'_556 v1
du_inject'8321'ℕ'60'_556 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_inject'8321'ℕ'60'_556 v0 = coe du_toℕ'60'n_156 (coe v0)
-- Data.Fin.Properties.inject₁ℕ≤
d_inject'8321'ℕ'8804'_566 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_inject'8321'ℕ'8804'_566 ~v0 v1 = du_inject'8321'ℕ'8804'_566 v1
du_inject'8321'ℕ'8804'_566 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_inject'8321'ℕ'8804'_566 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854
      (coe du_inject'8321'ℕ'60'_556 (coe v0))
-- Data.Fin.Properties.≤̄⇒inject₁<
d_'8804''772''8658'inject'8321''60'_568 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''772''8658'inject'8321''60'_568 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8804''772''8658'inject'8321''60'_568 v4
du_'8804''772''8658'inject'8321''60'_568 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''772''8658'inject'8321''60'_568 v0
  = coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v0
-- Data.Fin.Properties.ℕ<⇒inject₁<
d_ℕ'60''8658'inject'8321''60'_582 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ℕ'60''8658'inject'8321''60'_582 ~v0 v1 ~v2 v3
  = du_ℕ'60''8658'inject'8321''60'_582 v1 v3
du_ℕ'60''8658'inject'8321''60'_582 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ℕ'60''8658'inject'8321''60'_582 v0 v1
  = coe
      seq (coe v0)
      (coe
         du_'8804''772''8658'inject'8321''60'_568
         (coe
            MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v1)))
-- Data.Fin.Properties.i≤inject₁[j]⇒i≤1+j
d_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_588 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_588 ~v0 v1 ~v2 v3
                                                      v4
  = du_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_588 v1 v3 v4
du_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_588 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_i'8804'inject'8321''91'j'93''8658'i'8804'1'43'j_588 v0 v1 v2
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
-- Data.Fin.Properties.toℕ-lower₁
d_toℕ'45'lower'8321'_602 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'lower'8321'_602 = erased
-- Data.Fin.Properties.lower₁-injective
d_lower'8321''45'injective_620 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'8321''45'injective_620 = erased
-- Data.Fin.Properties.inject₁-lower₁
d_inject'8321''45'lower'8321'_644 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8321''45'lower'8321'_644 = erased
-- Data.Fin.Properties.lower₁-inject₁′
d_lower'8321''45'inject'8321''8242'_660 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'8321''45'inject'8321''8242'_660 = erased
-- Data.Fin.Properties.lower₁-inject₁
d_lower'8321''45'inject'8321'_668 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'8321''45'inject'8321'_668 = erased
-- Data.Fin.Properties.lower₁-irrelevant
d_lower'8321''45'irrelevant_678 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lower'8321''45'irrelevant_678 = erased
-- Data.Fin.Properties.inject₁≡⇒lower₁≡
d_inject'8321''8801''8658'lower'8321''8801'_694 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8321''8801''8658'lower'8321''8801'_694 = erased
-- Data.Fin.Properties.toℕ-inject≤
d_toℕ'45'inject'8804'_704 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inject'8804'_704 = erased
-- Data.Fin.Properties.inject≤-refl
d_inject'8804''45'refl_716 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'refl_716 = erased
-- Data.Fin.Properties.inject≤-idempotent
d_inject'8804''45'idempotent_732 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'idempotent_732 = erased
-- Data.Fin.Properties.inject≤-trans
d_inject'8804''45'trans_750 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'trans_750 = erased
-- Data.Fin.Properties.inject≤-injective
d_inject'8804''45'injective_762 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'injective_762 = erased
-- Data.Fin.Properties.inject≤-irrelevant
d_inject'8804''45'irrelevant_778 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'8804''45'irrelevant_778 = erased
-- Data.Fin.Properties.pred<
d_pred'60'_784 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'60'_784 ~v0 v1 ~v2 = du_pred'60'_784 v1
du_pred'60'_784 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pred'60'_784 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v2
        -> coe
             du_'8804''772''8658'inject'8321''60'_568
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
                (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.splitAt-↑ˡ
d_splitAt'45''8593''737'_796 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45''8593''737'_796 = erased
-- Data.Fin.Properties.splitAt⁻¹-↑ˡ
d_splitAt'8315''185''45''8593''737'_820 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'8315''185''45''8593''737'_820 = erased
-- Data.Fin.Properties.splitAt-↑ʳ
d_splitAt'45''8593''691'_854 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45''8593''691'_854 = erased
-- Data.Fin.Properties.splitAt⁻¹-↑ʳ
d_splitAt'8315''185''45''8593''691'_878 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'8315''185''45''8593''691'_878 = erased
-- Data.Fin.Properties.splitAt-join
d_splitAt'45'join_914 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45'join_914 = erased
-- Data.Fin.Properties.join-splitAt
d_join'45'splitAt_934 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_join'45'splitAt_934 = erased
-- Data.Fin.Properties.splitAt-<
d_splitAt'45''60'_974 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45''60'_974 = erased
-- Data.Fin.Properties.splitAt-≥
d_splitAt'45''8805'_992 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45''8805'_992 = erased
-- Data.Fin.Properties.+↔⊎
d_'43''8596''8846'_1002 ::
  Integer -> Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'43''8596''8846'_1002 v0 ~v1 = du_'43''8596''8846'_1002 v0
du_'43''8596''8846'_1002 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'43''8596''8846'_1002 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Fin.Base.du_splitAt_152 (coe v0))
      (coe MAlonzo.Code.Data.Fin.Base.du_join_166 (coe v0))
-- Data.Fin.Properties.remQuot-combine
d_remQuot'45'combine_1016 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_remQuot'45'combine_1016 = erased
-- Data.Fin.Properties.combine-remQuot
d_combine'45'remQuot_1046 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_combine'45'remQuot_1046 = erased
-- Data.Fin.Properties.toℕ-combine
d_toℕ'45'combine_1090 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'combine_1090 = erased
-- Data.Fin.Properties.combine-monoˡ-<
d_combine'45'mono'737''45''60'_1132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_combine'45'mono'737''45''60'_1132 ~v0 v1 v2 v3 v4 v5 v6
  = du_combine'45'mono'737''45''60'_1132 v1 v2 v3 v4 v5 v6
du_combine'45'mono'737''45''60'_1132 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_combine'45'mono'737''45''60'_1132 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v6)
         (coe
            MAlonzo.Code.Data.Fin.Base.du_toℕ_18
            (coe
               MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v1)
               (coe v3)))
         (coe
            MAlonzo.Code.Data.Fin.Base.du_toℕ_18
            (coe
               MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
               (coe v4)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v7 v8 v9 v10 v11 -> v11)
            (coe
               MAlonzo.Code.Data.Fin.Base.du_toℕ_18
               (coe
                  MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v1)
                  (coe v3)))
            (addInt
               (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v3))
               (coe
                  mulInt (coe v0)
                  (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))))
            (coe
               MAlonzo.Code.Data.Fin.Base.du_toℕ_18
               (coe
                  MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                  (coe v4)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (\ v7 v8 v9 v10 v11 ->
                     coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_2980 v8 v10 v11)
                  (coe
                     MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                  (\ v7 v8 v9 v10 v11 ->
                     coe
                       MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_2992
                       v10 v11))
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
                     MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                     (coe v4)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                  (\ v7 v8 v9 v10 v11 -> v11)
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
                        MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                        (coe v4)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v7 v8 v9 v10 v11 -> v11)
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
                           MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                           (coe v4)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                        (\ v7 v8 v9 v10 v11 -> v11)
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
                              MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                              (coe v4)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                              (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                              (\ v7 v8 v9 v10 v11 ->
                                 coe
                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986
                                   v10 v11))
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
                                 MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                                 (coe v4)))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                 (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                                 (\ v7 v8 v9 v10 v11 ->
                                    coe
                                      MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986
                                      v10 v11))
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
                                    MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                 (\ v7 v8 v9 v10 v11 -> v11)
                                 (addInt
                                    (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v4))
                                    (coe
                                       mulInt (coe v0)
                                       (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2))))
                                 (coe
                                    MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                                       (coe v4)))
                                 (coe
                                    MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                                       (coe v4)))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                       (coe
                                          MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810))
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0)
                                          (coe v2) (coe v4))))
                                 erased)
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3482
                                 (coe
                                    mulInt (coe v0)
                                    (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)))))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'691''45''8804'_4080
                              (coe v0) (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2))
                              (coe v5)))
                        erased)
                     erased)
                  erased)
               (coe
                  MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3596
                  (coe
                     mulInt (coe v0)
                     (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1)))
                  (coe du_toℕ'60'n_156 (coe v3))))
            erased))
-- Data.Fin.Properties.combine-injectiveˡ
d_combine'45'injective'737'_1162 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_combine'45'injective'737'_1162 = erased
-- Data.Fin.Properties.combine-injectiveʳ
d_combine'45'injective'691'_1222 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_combine'45'injective'691'_1222 = erased
-- Data.Fin.Properties.combine-injective
d_combine'45'injective_1254 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'injective_1254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_combine'45'injective_1254
du_combine'45'injective_1254 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'injective_1254
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Fin.Properties.combine-surjective
d_combine'45'surjective_1272 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_combine'45'surjective_1272 ~v0 v1 v2
  = du_combine'45'surjective_1272 v1 v2
du_combine'45'surjective_1272 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_combine'45'surjective_1272 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe
                 MAlonzo.Code.Data.Fin.Base.du_quotRem_178 (coe v0) (coe v1)) in
    coe
      (let v3
             = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Data.Fin.Base.du_quotRem_178 (coe v0) (coe v1)) in
       coe
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                  (\ v4 v5 v6 -> v6)
                  (coe
                     MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                     (coe v3))
                  v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                     erased
                     (coe
                        MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0) (coe v2)
                        (coe v3))
                     (coe
                        MAlonzo.Code.Data.Product.Base.du_uncurry_244
                        (coe MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0))
                        (coe MAlonzo.Code.Data.Fin.Base.du_remQuot_190 (coe v0) (coe v1)))
                     v1
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                        erased
                        (coe
                           MAlonzo.Code.Data.Product.Base.du_uncurry_244
                           (coe MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0))
                           (coe MAlonzo.Code.Data.Fin.Base.du_remQuot_190 (coe v0) (coe v1)))
                        v1 v1
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492 erased
                           (coe v1))
                        erased)
                     erased)))))
-- Data.Fin.Properties.*↔×
d_'42''8596''215'_1294 ::
  Integer -> Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'42''8596''215'_1294 ~v0 v1 = du_'42''8596''215'_1294 v1
du_'42''8596''215'_1294 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'42''8596''215'_1294 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Fin.Base.du_remQuot_190 (coe v0))
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (coe MAlonzo.Code.Data.Fin.Base.du_combine_208 (coe v0)))
-- Data.Fin.Properties.funToFin-finToFin
d_funToFin'45'finToFin_1300 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funToFin'45'finToFin_1300 = erased
-- Data.Fin.Properties.finToFun-funToFin
d_finToFun'45'funToFin_1316 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_finToFun'45'funToFin_1316 = erased
-- Data.Fin.Properties.^↔→
d_'94''8596''8594'_1342 ::
  Integer ->
  Integer ->
  (() ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'94''8596''8594'_1342 v0 v1 ~v2 = du_'94''8596''8594'_1342 v0 v1
du_'94''8596''8594'_1342 ::
  Integer -> Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'94''8596''8594'_1342 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe MAlonzo.Code.Data.Fin.Base.d_finToFun_224 (coe v0) (coe v1))
      (coe MAlonzo.Code.Data.Fin.Base.d_funToFin_240 (coe v1) (coe v0))
-- Data.Fin.Properties.lift-injective
d_lift'45'injective_1354 ::
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
d_lift'45'injective_1354 = erased
-- Data.Fin.Properties.<⇒≤pred
d_'60''8658''8804'pred_1378 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8658''8804'pred_1378 ~v0 v1 ~v2 v3 v4
  = du_'60''8658''8804'pred_1378 v1 v3 v4
du_'60''8658''8804'pred_1378 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''8658''8804'pred_1378 v0 v1 v2
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
                _                                           -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.toℕ‿ℕ-
d_toℕ'8255'ℕ'45'_1396 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'8255'ℕ'45'_1396 = erased
-- Data.Fin.Properties.ℕ-ℕ≡toℕ‿ℕ-
d_ℕ'45'ℕ'8801'toℕ'8255'ℕ'45'_1408 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ℕ'45'ℕ'8801'toℕ'8255'ℕ'45'_1408 = erased
-- Data.Fin.Properties.nℕ-ℕi≤n
d_nℕ'45'ℕi'8804'n_1420 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nℕ'45'ℕi'8804'n_1420 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2776
             (coe
                MAlonzo.Code.Data.Fin.Base.d__ℕ'45'ℕ__358 (coe v0)
                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                   (\ v5 v6 v7 ->
                      coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2854 v7))
                (MAlonzo.Code.Data.Fin.Base.d__ℕ'45'ℕ__358
                   (coe v0) (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3))
                v0
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                      (\ v5 v6 v7 v8 v9 ->
                         coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v8
                           v9))
                   (MAlonzo.Code.Data.Fin.Base.d__ℕ'45'ℕ__358 (coe v4) (coe v3)) v4 v0
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810)
                         (\ v5 v6 v7 v8 v9 ->
                            coe
                              MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_2986 v8
                              v9))
                      v4 v0 v0
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2810))
                         (coe v0))
                      (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2844 (coe v4)))
                   (d_nℕ'45'ℕi'8804'n_1420 (coe v4) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.punchIn-injective
d_punchIn'45'injective_1438 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchIn'45'injective_1438 = erased
-- Data.Fin.Properties.punchInᵢ≢i
d_punchIn'7522''8802'i_1454 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_punchIn'7522''8802'i_1454 = erased
-- Data.Fin.Properties.punchOut-cong
d_punchOut'45'cong_1470 ::
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
d_punchOut'45'cong_1470 = erased
-- Data.Fin.Properties.punchOut-cong′
d_punchOut'45'cong'8242'_1504 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchOut'45'cong'8242'_1504 = erased
-- Data.Fin.Properties.punchOut-injective
d_punchOut'45'injective_1520 ::
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
d_punchOut'45'injective_1520 = erased
-- Data.Fin.Properties.punchIn-punchOut
d_punchIn'45'punchOut_1556 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchIn'45'punchOut_1556 = erased
-- Data.Fin.Properties.punchOut-punchIn
d_punchOut'45'punchIn_1580 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchOut'45'punchIn_1580 = erased
-- Data.Fin.Properties.pinch-surjective
d_pinch'45'surjective_1596 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pinch'45'surjective_1596 ~v0 v1 v2
  = du_pinch'45'surjective_1596 v1 v2
du_pinch'45'surjective_1596 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pinch'45'surjective_1596 v0 v1
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
                    (coe du_pinch'45'surjective_1596 (coe v5) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties..extendedlambda8
d_'46'extendedlambda8_1598 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda8_1598 = erased
-- Data.Fin.Properties..extendedlambda9
d_'46'extendedlambda9_1602 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda9_1602 = erased
-- Data.Fin.Properties..extendedlambda10
d_'46'extendedlambda10_1608 ::
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
d_'46'extendedlambda10_1608 = erased
-- Data.Fin.Properties.pinch-mono-≤
d_pinch'45'mono'45''8804'_1614 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pinch'45'mono'45''8804'_1614 ~v0 v1 v2 v3 v4
  = du_pinch'45'mono'45''8804'_1614 v1 v2 v3 v4
du_pinch'45'mono'45''8804'_1614 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pinch'45'mono'45''8804'_1614 v0 v1 v2 v3
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
                              du_pinch'45'mono'45''8804'_1614 (coe v5) (coe v7) (coe v9)
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v3)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.pinch-injective
d_pinch'45'injective_1646 ::
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
d_pinch'45'injective_1646 = erased
-- Data.Fin.Properties._.∀-cons
d_'8704''45'cons_1690 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  AgdaAny ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_'8704''45'cons_1690 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8704''45'cons_1690 v3 v4 v5
du_'8704''45'cons_1690 ::
  AgdaAny ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_'8704''45'cons_1690 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12   -> coe v0
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4 -> coe v1 v4
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties._.∀-cons-⇔
d_'8704''45'cons'45''8660'_1702 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8704''45'cons'45''8660'_1702 ~v0 ~v1 ~v2
  = du_'8704''45'cons'45''8660'_1702
du_'8704''45'cons'45''8660'_1702 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8704''45'cons'45''8660'_1702
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
      (coe
         MAlonzo.Code.Data.Product.Base.du_uncurry_244
         (coe du_'8704''45'cons_1690))
      (coe
         MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
         (coe (\ v0 -> coe v0 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            (\ v0 v1 -> coe v0 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v1))))
-- Data.Fin.Properties._.∃-here
d_'8707''45'here_1708 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8707''45'here_1708 ~v0 ~v1 ~v2 v3 = du_'8707''45'here_1708 v3
du_'8707''45'here_1708 ::
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8707''45'here_1708 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v0)
-- Data.Fin.Properties._.∃-there
d_'8707''45'there_1712 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8707''45'there_1712 ~v0 ~v1 ~v2 = du_'8707''45'there_1712
du_'8707''45'there_1712 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8707''45'there_1712
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe MAlonzo.Code.Data.Fin.Base.C_suc_16) (coe (\ v0 v1 -> v1))
-- Data.Fin.Properties._.∃-toSum
d_'8707''45'toSum_1714 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8707''45'toSum_1714 ~v0 ~v1 ~v2 v3 = du_'8707''45'toSum_1714 v3
du_'8707''45'toSum_1714 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8707''45'toSum_1714 v0
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
d_'8846''8660''8707'_1722 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8846''8660''8707'_1722 ~v0 ~v1 ~v2 = du_'8846''8660''8707'_1722
du_'8846''8660''8707'_1722 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8846''8660''8707'_1722
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
         (coe du_'8707''45'here_1708) (coe du_'8707''45'there_1712))
      (coe du_'8707''45'toSum_1714)
-- Data.Fin.Properties.decFinSubset
d_decFinSubset_1734 ::
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
d_decFinSubset_1734 v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_decFinSubset_1734 v0 v5 v6
du_decFinSubset_1734 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decFinSubset_1734 v0 v1 v2
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v4 = coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) in
              coe
                (let v5 = coe du_'8704''45'cons_1690 in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
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
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                                       (coe
                                          v2 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                                             (coe v7)))
                                       (coe
                                          du_decFinSubset_1734 (coe v3)
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
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                                    (coe
                                       (\ v8 v9 ->
                                          coe
                                            v5
                                            (\ v10 ->
                                               coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14)
                                            (\ v10 -> coe v8 v10) v9))
                                    (coe
                                       (\ v8 v9 ->
                                          coe v8 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v9)))
                                    (coe
                                       du_decFinSubset_1734 (coe v3)
                                       (coe
                                          (\ v8 ->
                                             coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8)))
                                       (coe
                                          (\ v8 ->
                                             coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8))))
                      _ -> MAlonzo.RTE.mazUnreachableError)))
-- Data.Fin.Properties.any?
d_any'63'_1814 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_any'63'_1814 v0 ~v1 ~v2 v3 = du_any'63'_1814 v0 v3
du_any'63'_1814 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_any'63'_1814 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
                (coe du_'8846''8660''8707'_1722)
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__86
                   (coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                   (coe
                      du_any'63'_1814 (coe v2)
                      (coe
                         (\ v3 -> coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3))))))
-- Data.Fin.Properties.all?
d_all'63'_1832 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_all'63'_1832 v0 ~v1 ~v2 v3 = du_all'63'_1832 v0 v3
du_all'63'_1832 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_all'63'_1832 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      (coe
         (\ v2 v3 -> coe v2 v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      (coe (\ v2 v3 v4 -> coe v2 v3))
      (coe
         du_decFinSubset_1734 (coe v0)
         (\ v2 -> coe MAlonzo.Code.Relation.Unary.Properties.du_U'63'_34)
         (coe (\ v2 v3 -> coe v1 v2)))
-- Data.Fin.Properties.¬∀⟶∃¬-smallest
d_'172''8704''10230''8707''172''45'smallest_1874 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  ((MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'172''8704''10230''8707''172''45'smallest_1874 v0 ~v1 ~v2 v3 ~v4
  = du_'172''8704''10230''8707''172''45'smallest_1874 v0 v3
du_'172''8704''10230''8707''172''45'smallest_1874 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'172''8704''10230''8707''172''45'smallest_1874 v0 v1
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
                                                 du_'8704''45'cons_1690
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                                                    (coe v5))))))
                                 (coe
                                    du_'172''8704''10230''8707''172''45'smallest_1874 (coe v2)
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
d_'172''8704''10230''8707''172'_1924 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  ((MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'172''8704''10230''8707''172'_1924 v0 ~v1 ~v2 v3 ~v4
  = du_'172''8704''10230''8707''172'_1924 v0 v3
du_'172''8704''10230''8707''172'_1924 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'172''8704''10230''8707''172'_1924 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128 (coe (\ v2 -> v2))
      (coe
         (\ v2 v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         du_'172''8704''10230''8707''172''45'smallest_1874 (coe v0)
         (coe v1))
-- Data.Fin.Properties.pigeonhole
d_pigeonhole_1940 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pigeonhole_1940 ~v0 v1 v2 v3 = du_pigeonhole_1940 v1 v2 v3
du_pigeonhole_1940 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pigeonhole_1940 v0 v1 v2
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
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                               (coe
                                  MAlonzo.Code.Function.Bundles.d_to_1724
                                  (coe du_'8846''8660''8707'_1722))
                               (coe
                                  MAlonzo.Code.Function.Bundles.d_from_1726
                                  (coe du_'8846''8660''8707'_1722))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__86
                                  (coe
                                     du__'8799'__50
                                     (coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                     (coe
                                        v2
                                        (coe
                                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                  (coe
                                     du_any'63'_1814 (coe v9)
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
                                                   du_pigeonhole_1940
                                                   (coe subInt (coe v0) (coe (1 :: Integer)))
                                                   (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8)
                                                   (coe
                                                      (\ v13 ->
                                                         coe
                                                           MAlonzo.Code.Data.Fin.Base.du_punchOut_382
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
d_injective'8658''8804'_1988 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_injective'8658''8804'_1988 v0 v1 ~v2 ~v3
  = du_injective'8658''8804'_1988 v0 v1
du_injective'8658''8804'_1988 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_injective'8658''8804'_1988 v0 v1
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
                          (coe du_injective'8658''8804'_1988 (coe v2) (coe v3))))
-- Data.Fin.Properties.<⇒notInjective
d_'60''8658'notInjective_2002 ::
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
d_'60''8658'notInjective_2002 = erased
-- Data.Fin.Properties.ℕ→Fin-notInjective
d_ℕ'8594'Fin'45'notInjective_2010 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ℕ'8594'Fin'45'notInjective_2010 = erased
-- Data.Fin.Properties.cantor-schröder-bernstein
d_cantor'45'schröder'45'bernstein_2020 ::
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
d_cantor'45'schröder'45'bernstein_2020 = erased
-- Data.Fin.Properties._.sequence
d_sequence_2078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> ()) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
d_sequence_2078 ~v0 ~v1 v2 v3 ~v4 v5 = du_sequence_2078 v2 v3 v5
du_sequence_2078 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> AgdaAny
du_sequence_2078 v0 v1 v2
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
                   erased (coe du_'8704''45'cons_1690)
                   (coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                (coe
                   du_sequence_2078 (coe v0) (coe v3)
                   (coe
                      (\ v4 -> coe v2 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v4)))))
-- Data.Fin.Properties._.sequence⁻¹
d_sequence'8315''185'_2114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny
d_sequence'8315''185'_2114 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_sequence'8315''185'_2114 v2 v5 v6
du_sequence'8315''185'_2114 ::
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_sequence'8315''185'_2114 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30 v0 erased erased
      (\ v3 -> coe v3 v2) v1
-- Data.Fin.Properties._._._≈_
d__'8776'__2138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__2138 = erased
-- Data.Fin.Properties._.inj⇒≟
d_inj'8658''8799'_2158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_inj'8658''8799'_2158 ~v0 ~v1 ~v2 ~v3 v4
  = du_inj'8658''8799'_2158 v4
du_inj'8658''8799'_2158 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_inj'8658''8799'_2158 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.du_via'45'injection_160
      (coe v0) (coe du__'8799'__50)
-- Data.Fin.Properties._.inj⇒decSetoid
d_inj'8658'decSetoid_2160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_inj'8658'decSetoid_2160 ~v0 ~v1 ~v2 v3 v4
  = du_inj'8658'decSetoid_2160 v3 v4
du_inj'8658'decSetoid_2160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
du_inj'8658'decSetoid_2160 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1389
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
         (coe du_inj'8658''8799'_2158 (coe v1)))
-- Data.Fin.Properties.opposite-prop
d_opposite'45'prop_2164 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'prop_2164 = erased
-- Data.Fin.Properties.opposite-involutive
d_opposite'45'involutive_2176 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'involutive_2176 = erased
-- Data.Fin.Properties.opposite-suc
d_opposite'45'suc_2190 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_opposite'45'suc_2190 = erased
-- Data.Fin.Properties.inject+-raise-splitAt
d_inject'43''45'raise'45'splitAt_2200 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'43''45'raise'45'splitAt_2200 = erased
-- Data.Fin.Properties.toℕ-raise
d_toℕ'45'raise_2202 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'raise_2202 = erased
-- Data.Fin.Properties.toℕ-inject+
d_toℕ'45'inject'43'_2210 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toℕ'45'inject'43'_2210 = erased
-- Data.Fin.Properties.splitAt-inject+
d_splitAt'45'inject'43'_2222 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45'inject'43'_2222 = erased
-- Data.Fin.Properties.splitAt-raise
d_splitAt'45'raise_2236 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45'raise_2236 = erased
-- Data.Fin.Properties.Fin0↔⊥
d_Fin0'8596''8869'_2238 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_Fin0'8596''8869'_2238 = coe d_0'8596''8869'_24
-- Data.Fin.Properties.eq?
d_eq'63'_2240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eq'63'_2240 ~v0 ~v1 ~v2 = du_eq'63'_2240
du_eq'63'_2240 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_eq'63'_2240 = coe du_inj'8658''8799'_2158
-- Data.Fin.Properties.z≺s
d_z'8826's_2244 ::
  Integer -> MAlonzo.Code.Data.Fin.Base.T__'8826'__518
d_z'8826's_2244 ~v0 = du_z'8826's_2244
du_z'8826's_2244 :: MAlonzo.Code.Data.Fin.Base.T__'8826'__518
du_z'8826's_2244
  = coe
      MAlonzo.Code.Data.Fin.Base.C__'8827'toℕ__524
      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
-- Data.Fin.Properties.s≺s
d_s'8826's_2250 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518
d_s'8826's_2250 ~v0 ~v1 v2 = du_s'8826's_2250 v2
du_s'8826's_2250 ::
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518
du_s'8826's_2250 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C__'8827'toℕ__524 v2
        -> coe
             MAlonzo.Code.Data.Fin.Base.C__'8827'toℕ__524
             (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.<⇒≺
d_'60''8658''8826'_2256 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518
d_'60''8658''8826'_2256 v0 ~v1 v2 = du_'60''8658''8826'_2256 v0 v2
du_'60''8658''8826'_2256 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518
du_'60''8658''8826'_2256 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
               -> coe seq (coe v4) (coe du_z'8826's_2244)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe
                       du_s'8826's_2250 (coe du_'60''8658''8826'_2256 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Properties.≺⇒<
d_'8826''8658''60'_2262 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8826''8658''60'_2262 ~v0 ~v1 v2 = du_'8826''8658''60'_2262 v2
du_'8826''8658''60'_2262 ::
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8826''8658''60'_2262 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C__'8827'toℕ__524 v2
        -> coe du_toℕ'60'n_156 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Properties.≺⇒<′
d_'8826''8658''60''8242'_2268 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_'8826''8658''60''8242'_2268 ~v0 v1 v2
  = du_'8826''8658''60''8242'_2268 v1 v2
du_'8826''8658''60''8242'_2268 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
du_'8826''8658''60''8242'_2268 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''8658''60''8242'_6146
      (coe v0) (coe du_'8826''8658''60'_2262 (coe v1))
-- Data.Fin.Properties.<′⇒≺
d_'60''8242''8658''8826'_2272 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518
d_'60''8242''8658''8826'_2272 v0 ~v1 v2
  = du_'60''8242''8658''8826'_2272 v0 v2
du_'60''8242''8658''8826'_2272 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Fin.Base.T__'8826'__518
du_'60''8242''8658''8826'_2272 v0 v1
  = coe
      du_'60''8658''8826'_2256 (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8242''8658''60'_6150
         (coe v0) (coe v1))
