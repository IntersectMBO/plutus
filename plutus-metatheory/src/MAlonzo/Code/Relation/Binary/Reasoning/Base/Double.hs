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

module MAlonzo.Code.Relation.Binary.Reasoning.Base.Double where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Binary.Reasoning.Base.Double._IsRelatedTo_
d__IsRelatedTo__62 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T__IsRelatedTo__62
  = C_nonstrict_70 AgdaAny | C_equals_74 AgdaAny
-- Relation.Binary.Reasoning.Base.Double.start
d_start_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> AgdaAny
d_start_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_start_76 v6 v7 v8 v9
du_start_76 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> AgdaAny
du_start_76 v0 v1 v2 v3
  = case coe v3 of
      C_nonstrict_70 v4 -> coe v4
      C_equals_74 v4
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 v0 v1 v2 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Reasoning.Base.Double.≡-go
d_'8801''45'go_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62 -> T__IsRelatedTo__62
d_'8801''45'go_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_'8801''45'go_82 v11
du_'8801''45'go_82 :: T__IsRelatedTo__62 -> T__IsRelatedTo__62
du_'8801''45'go_82 v0 = coe v0
-- Relation.Binary.Reasoning.Base.Double..extendedlambda0
d_'46'extendedlambda0_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'46'extendedlambda0_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11 ~v12
  = du_'46'extendedlambda0_88 v11
du_'46'extendedlambda0_88 :: AgdaAny -> AgdaAny
du_'46'extendedlambda0_88 v0 = coe v0
-- Relation.Binary.Reasoning.Base.Double..extendedlambda1
d_'46'extendedlambda1_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'46'extendedlambda1_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11 ~v12
  = du_'46'extendedlambda1_94 v11
du_'46'extendedlambda1_94 :: AgdaAny -> AgdaAny
du_'46'extendedlambda1_94 v0 = coe v0
-- Relation.Binary.Reasoning.Base.Double.≲-go
d_'8818''45'go_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> T__IsRelatedTo__62
d_'8818''45'go_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_'8818''45'go_96 v6 v7 v8 v9 v10 v11
du_'8818''45'go_96 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> T__IsRelatedTo__62
du_'8818''45'go_96 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_nonstrict_70 v6
        -> coe
             C_nonstrict_70
             (coe
                MAlonzo.Code.Relation.Binary.Structures.d_trans_90 v0 v1 v2 v3 v4
                v6)
      C_equals_74 v6
        -> coe
             C_nonstrict_70
             (coe
                MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                v0 v1 v2 v3 v6 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Reasoning.Base.Double.≈-go
d_'8776''45'go_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> T__IsRelatedTo__62
d_'8776''45'go_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_'8776''45'go_106 v6 v7 v8 v9 v10 v11
du_'8776''45'go_106 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> T__IsRelatedTo__62
du_'8776''45'go_106 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_nonstrict_70 v6
        -> coe
             C_nonstrict_70
             (coe
                MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                v0 v3 v2 v1
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                   (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                      (coe v0))
                   v1 v2 v4)
                v6)
      C_equals_74 v6
        -> coe
             C_equals_74
             (coe
                MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                   (coe v0))
                v1 v2 v3 v4 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Reasoning.Base.Double.stop
d_stop_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> T__IsRelatedTo__62
d_stop_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_stop_116 v6 v7
du_stop_116 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> T__IsRelatedTo__62
du_stop_116 v0 v1
  = coe
      C_equals_74
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v0))
         v1)
-- Relation.Binary.Reasoning.Base.Double.IsEquality
d_IsEquality_122 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsEquality_122 = C_isEquality_130
-- Relation.Binary.Reasoning.Base.Double.IsEquality?
d_IsEquality'63'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_IsEquality'63'_138 v9
du_IsEquality'63'_138 ::
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_IsEquality'63'_138 v0
  = case coe v0 of
      C_nonstrict_70 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      C_equals_74 v1
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe C_isEquality_130))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Reasoning.Base.Double.extractEquality
d_extractEquality_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> T_IsEquality_122 -> AgdaAny
d_extractEquality_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_extractEquality_148 v9 v10
du_extractEquality_148 ::
  T__IsRelatedTo__62 -> T_IsEquality_122 -> AgdaAny
du_extractEquality_148 v0 v1
  = coe
      seq (coe v1)
      (case coe v0 of
         C_equals_74 v2 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Reasoning.Base.Double.equalitySubRelation
d_equalitySubRelation_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_equalitySubRelation_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_equalitySubRelation_152
du_equalitySubRelation_152 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
du_equalitySubRelation_152
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.C_constructor_94
      (\ v0 v1 v2 -> coe du_IsEquality'63'_138 v2)
      (\ v0 v1 v2 v3 -> coe du_extractEquality_148 v2 v3)
-- Relation.Binary.Reasoning.Base.Double._.begin_
d_begin__156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> AgdaAny
d_begin__156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_begin__156 v6
du_begin__156 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> AgdaAny
du_begin__156 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe du_start_76 (coe v0))
-- Relation.Binary.Reasoning.Base.Double._.begin_
d_begin__160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> AgdaAny
d_begin__160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_begin__160
du_begin__160 ::
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> AgdaAny
du_begin__160
  = let v0 = coe du_equalitySubRelation_152 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
           (coe v0) v1 v2 v3)
-- Relation.Binary.Reasoning.Base.Double._.step-≡
d_step'45''8801'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62
d_step'45''8801'_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_step'45''8801'_164
du_step'45''8801'_164 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62
du_step'45''8801'_164
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Base.Double._.step-≡-∣
d_step'45''8801''45''8739'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__62 -> T__IsRelatedTo__62
d_step'45''8801''45''8739'_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_step'45''8801''45''8739'_166 v9
du_step'45''8801''45''8739'_166 ::
  T__IsRelatedTo__62 -> T__IsRelatedTo__62
du_step'45''8801''45''8739'_166 v0 = coe v0
-- Relation.Binary.Reasoning.Base.Double._.step-≡-⟨
d_step'45''8801''45''10216'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62
d_step'45''8801''45''10216'_168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_step'45''8801''45''10216'_168
du_step'45''8801''45''10216'_168 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62
du_step'45''8801''45''10216'_168
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Base.Double._.step-≡-⟩
d_step'45''8801''45''10217'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62
d_step'45''8801''45''10217'_170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_step'45''8801''45''10217'_170
du_step'45''8801''45''10217'_170 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62
du_step'45''8801''45''10217'_170
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Base.Double._.step-≡˘
d_step'45''8801''728'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62
d_step'45''8801''728'_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_step'45''8801''728'_172
du_step'45''8801''728'_172 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__62
du_step'45''8801''728'_172
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_454
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Base.Double._.step-≈
d_step'45''8776'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
d_step'45''8776'_176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_step'45''8776'_176 v6
du_step'45''8776'_176 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
du_step'45''8776'_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776'_374
      (coe du_'8776''45'go_106 (coe v0))
-- Relation.Binary.Reasoning.Base.Double._.step-≈-⟨
d_step'45''8776''45''10216'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
d_step'45''8776''45''10216'_178 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_step'45''8776''45''10216'_178 v6
du_step'45''8776''45''10216'_178 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
du_step'45''8776''45''10216'_178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
      (coe du_'8776''45'go_106 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v0)))
-- Relation.Binary.Reasoning.Base.Double._.step-≈-⟩
d_step'45''8776''45''10217'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
d_step'45''8776''45''10217'_180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_step'45''8776''45''10217'_180 v6
du_step'45''8776''45''10217'_180 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
du_step'45''8776''45''10217'_180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
      (coe du_'8776''45'go_106 (coe v0))
-- Relation.Binary.Reasoning.Base.Double._.step-≈˘
d_step'45''8776''728'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
d_step'45''8776''728'_182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_step'45''8776''728'_182 v6
du_step'45''8776''728'_182 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
du_step'45''8776''728'_182 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''728'_376
      (coe du_'8776''45'go_106 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v0)))
-- Relation.Binary.Reasoning.Base.Double._.step-≲
d_step'45''8818'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
d_step'45''8818'_186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_step'45''8818'_186 v6
du_step'45''8818'_186 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
du_step'45''8818'_186 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8818'_306
      (coe du_'8818''45'go_96 (coe v0))
-- Relation.Binary.Reasoning.Base.Double._._∎
d__'8718'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> T__IsRelatedTo__62
d__'8718'_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du__'8718'_190 v6
du__'8718'_190 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny -> T__IsRelatedTo__62
du__'8718'_190 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
      (coe du_stop_116 (coe v0))
-- Relation.Binary.Reasoning.Base.Double._.step-∼
d_step'45''8764'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
d_step'45''8764'_194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_step'45''8764'_194 v6
du_step'45''8764'_194 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__62 -> AgdaAny -> T__IsRelatedTo__62
du_step'45''8764'_194 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_302
      (coe du_'8818''45'go_96 (coe v0))
