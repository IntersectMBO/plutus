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

module MAlonzo.Code.Relation.Binary.Reasoning.Preorder where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Double qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Reasoning.Preorder._._IsRelatedTo_
d__IsRelatedTo__80 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Reasoning.Preorder._._∎
d__'8718'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d__'8718'_82 ~v0 ~v1 ~v2 v3 = du__'8718'_82 v3
du__'8718'_82 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du__'8718'_82 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
            (coe v1)))
-- Relation.Binary.Reasoning.Preorder._.IsEquality
d_IsEquality_84 a0 a1 a2 a3 a4 a5 a6 = ()
-- Relation.Binary.Reasoning.Preorder._.IsEquality?
d_IsEquality'63'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_86 ~v0 ~v1 ~v2 ~v3 = du_IsEquality'63'_86
du_IsEquality'63'_86 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_IsEquality'63'_86 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_IsEquality'63'_138
      v2
-- Relation.Binary.Reasoning.Preorder._.begin_
d_begin__88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny
d_begin__88 ~v0 ~v1 ~v2 v3 = du_begin__88 v3
du_begin__88 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny
du_begin__88 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
            (coe v1)))
-- Relation.Binary.Reasoning.Preorder._.begin_
d_begin__90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny -> AgdaAny
d_begin__90 ~v0 ~v1 ~v2 ~v3 = du_begin__90
du_begin__90 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny -> AgdaAny
du_begin__90
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Relation.Binary.Reasoning.Preorder._.equalitySubRelation
d_equalitySubRelation_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_equalitySubRelation_92 ~v0 ~v1 ~v2 ~v3
  = du_equalitySubRelation_92
du_equalitySubRelation_92 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
du_equalitySubRelation_92
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152
-- Relation.Binary.Reasoning.Preorder._.extractEquality
d_extractEquality_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T_IsEquality_122 ->
  AgdaAny
d_extractEquality_96 ~v0 ~v1 ~v2 ~v3 = du_extractEquality_96
du_extractEquality_96 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T_IsEquality_122 ->
  AgdaAny
du_extractEquality_96 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_extractEquality_148
      v2 v3
-- Relation.Binary.Reasoning.Preorder._.start
d_start_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny
d_start_102 ~v0 ~v1 ~v2 v3 = du_start_102 v3
du_start_102 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny
du_start_102 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))
-- Relation.Binary.Reasoning.Preorder._.step-∼
d_step'45''8764'_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8764'_104 ~v0 ~v1 ~v2 v3 = du_step'45''8764'_104 v3
du_step'45''8764'_104 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8764'_104 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
            (coe v1)))
-- Relation.Binary.Reasoning.Preorder._.step-≈
d_step'45''8776'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776'_106 ~v0 ~v1 ~v2 v3 = du_step'45''8776'_106 v3
du_step'45''8776'_106 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8776'_106 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe v1)))
-- Relation.Binary.Reasoning.Preorder._.step-≈-⟨
d_step'45''8776''45''10216'_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''45''10216'_108 ~v0 ~v1 ~v2 v3
  = du_step'45''8776''45''10216'_108 v3
du_step'45''8776''45''10216'_108 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8776''45''10216'_108 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
               (coe v1))))
-- Relation.Binary.Reasoning.Preorder._.step-≈-⟩
d_step'45''8776''45''10217'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''45''10217'_110 ~v0 ~v1 ~v2 v3
  = du_step'45''8776''45''10217'_110 v3
du_step'45''8776''45''10217'_110 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8776''45''10217'_110 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe v1)))
-- Relation.Binary.Reasoning.Preorder._.step-≈˘
d_step'45''8776''728'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''728'_112 ~v0 ~v1 ~v2 v3
  = du_step'45''8776''728'_112 v3
du_step'45''8776''728'_112 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8776''728'_112 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''728'_374
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
               (coe v1))))
-- Relation.Binary.Reasoning.Preorder._.step-≡
d_step'45''8801'_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801'_114 ~v0 ~v1 ~v2 ~v3 = du_step'45''8801'_114
du_step'45''8801'_114 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801'_114
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Preorder._.step-≡-∣
d_step'45''8801''45''8739'_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''8739'_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_step'45''8801''45''8739'_116 v6
du_step'45''8801''45''8739'_116 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''45''8739'_116 v0 = coe v0
-- Relation.Binary.Reasoning.Preorder._.step-≡-⟨
d_step'45''8801''45''10216'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''10216'_118 ~v0 ~v1 ~v2 ~v3
  = du_step'45''8801''45''10216'_118
du_step'45''8801''45''10216'_118 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''45''10216'_118
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Preorder._.step-≡-⟩
d_step'45''8801''45''10217'_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''10217'_120 ~v0 ~v1 ~v2 ~v3
  = du_step'45''8801''45''10217'_120
du_step'45''8801''45''10217'_120 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''45''10217'_120
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Preorder._.step-≡˘
d_step'45''8801''728'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''728'_122 ~v0 ~v1 ~v2 ~v3
  = du_step'45''8801''728'_122
du_step'45''8801''728'_122 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''728'_122
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Preorder._.step-≲
d_step'45''8818'_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8818'_124 ~v0 ~v1 ~v2 v3 = du_step'45''8818'_124 v3
du_step'45''8818'_124 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8818'_124 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8818'_304
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
            (coe v1)))
-- Relation.Binary.Reasoning.Preorder._.stop
d_stop_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_stop_126 ~v0 ~v1 ~v2 v3 = du_stop_126 v3
du_stop_126 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_stop_126 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))
-- Relation.Binary.Reasoning.Preorder._.≈-go
d_'8776''45'go_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8776''45'go_128 ~v0 ~v1 ~v2 v3 = du_'8776''45'go_128 v3
du_'8776''45'go_128 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_'8776''45'go_128 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))
-- Relation.Binary.Reasoning.Preorder._.≡-go
d_'8801''45'go_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8801''45'go_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8801''45'go_130 v8
du_'8801''45'go_130 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_'8801''45'go_130 v0 = coe v0
-- Relation.Binary.Reasoning.Preorder._.≲-go
d_'8818''45'go_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8818''45'go_132 ~v0 ~v1 ~v2 v3 = du_'8818''45'go_132 v3
du_'8818''45'go_132 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_'8818''45'go_132 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))
